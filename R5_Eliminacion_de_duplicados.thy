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
  "sinDuplicados xs = undefined"

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
  "borraDuplicados xs = undefined"

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
oops

text {*
  --------------------------------------------------------------------- 
  Ejercicio 4.2. Demostrar o refutar detalladamente
     length (borraDuplicados xs) \<le> length xs
  --------------------------------------------------------------------- 
*}

-- "La demostración estructurada es"
lemma length_borraDuplicados_2: 
  "length (borraDuplicados xs) \<le> length xs"
oops

text {*
  --------------------------------------------------------------------- 
  Ejercicio 5.1. Demostrar o refutar automáticamente
     estaEn a (borraDuplicados xs) = estaEn a xs
  --------------------------------------------------------------------- 
*}

-- "La demostración automática es"
lemma estaEn_borraDuplicados: 
  "estaEn a (borraDuplicados xs) = estaEn a xs"
oops

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
lemma estaEn_borraDuplicados_2: 
  "estaEn a (borraDuplicados xs) = estaEn a xs"
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
oops

text {*
  --------------------------------------------------------------------- 
  Ejercicio 6.2. Demostrar o refutar detalladamente
     sinDuplicados (borraDuplicados xs)
  --------------------------------------------------------------------- 
*}

-- "La demostración estructurada es"
lemma sinDuplicados_borraDuplicados_2:
  "sinDuplicados (borraDuplicados xs)"
oops

text {*
  --------------------------------------------------------------------- 
  Ejercicio 7. Demostrar o refutar:
    borraDuplicados (rev xs) = rev (borraDuplicados xs)
  --------------------------------------------------------------------- 
*}

end