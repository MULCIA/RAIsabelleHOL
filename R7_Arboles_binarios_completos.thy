chapter {* R7: Árboles binarios completos *}

theory R7_Arboles_binarios_completos
imports Main 
begin 

text {*  
  En esta relación se piden demostraciones automáticas (lo más cortas
  posibles). Para ello, en algunos casos es necesario incluir lemas
  auxiliares (que se demuestran automáticamente) y usar ejercicios
  anteriores. 

  --------------------------------------------------------------------- 
  Ejercicio 1. Definir el tipo de datos arbol para representar los
  árboles binarios que no tienen información ni en los nodos y ni en las
  hojas. Por ejemplo, el árbol
          ·
         / \
        /   \
       ·     ·
      / \   / \
     ·   · ·   · 
  se representa por "N (N H H) (N H H)".
  --------------------------------------------------------------------- 
*}

datatype arbol = H | N arbol arbol

value "N (N H H) (N H H) = (N (N H H) (N H H) :: arbol)"

text {*  
  --------------------------------------------------------------------- 
  Ejercicio 2. Definir la función
     hojas :: "arbol => nat" 
  tal que (hojas a) es el número de hojas del árbol a. Por ejemplo,
     hojas (N (N H H) (N H H)) = 4
  --------------------------------------------------------------------- 
*}

fun hojas :: "arbol => nat" where
  "hojas H = 1"
| "hojas (N i d) = hojas i + hojas d"

value "hojas (N (N H H) (N H H)) = 4"

text {*  
  --------------------------------------------------------------------- 
  Ejercicio 4. Definir la función
     profundidad :: "arbol => nat" 
  tal que (profundidad a) es la profundidad del árbol a. Por ejemplo,
     profundidad (N (N H H) (N H H)) = 2
  --------------------------------------------------------------------- 
*}

fun profundidad :: "arbol => nat" where
  "profundidad H = 0"
| "profundidad (N i d) = 1 + (max (profundidad i)(profundidad d))"

value "profundidad (N (N H H) (N H H)) = 2"

text {*  
  --------------------------------------------------------------------- 
  Ejercicio 5. Definir la función
     abc :: "nat \<Rightarrow> arbol" 
  tal que (abc n) es el árbol binario completo de profundidad n. Por
  ejemplo,  
     abc 3 = N (N (N H H) (N H H)) (N (N H H) (N H H))
  --------------------------------------------------------------------- 
*}

fun abc :: "nat \<Rightarrow> arbol" where
  "abc 0 = H"
| "abc (Suc n) = (N (abc n) (abc n))"

value "abc 3 = N (N (N H H) (N H H)) (N (N H H) (N H H))"

text {*  
  --------------------------------------------------------------------- 
  Ejercicio 6. Un árbol binario a es completo respecto de la medida f si
  a es una hoja o bien a es de la forma (N i d) y se cumple que tanto i
  como d son árboles binarios completos respecto de f y, además, 
  f(i) = f(r).

  Definir la función
     es_abc :: "(arbol => 'a) => arbol => bool
  tal que (es_abc f a) se verifica si a es un árbol binario completo
  respecto de f.
  --------------------------------------------------------------------- 
*}

fun es_abc :: "(arbol => 'a) => arbol => bool" where
  "es_abc _ H = True"
|  "es_abc f (N i d) = (es_abc f i \<and> es_abc f d \<and> (f i = f d))"

text {*  
  --------------------------------------------------------------------- 
  Nota. (size a) es el número de nodos del árbol a. Por ejemplo,
     size (N (N H H) (N H H)) = 3
  --------------------------------------------------------------------- 
*}

value "size (N (N H H) (N H H)) = 3"
value "size (N (N (N H H) (N H H)) (N (N H H) (N H H))) = 7"

text {*  
  --------------------------------------------------------------------- 
  Nota. Tenemos 3 funciones de medida sobre los árboles: número de
  hojas, número de nodos y profundidad. A cada una le corresponde un
  concepto de completitud. En los siguientes ejercicios demostraremos
  que los tres conceptos de completitud son iguales.
  --------------------------------------------------------------------- 
*}

text {*  
  --------------------------------------------------------------------- 
  Ejercicio 7. Demostrar que un árbol binario a es completo respecto de
  la profundidad syss es completo respecto del número de hojas.
  --------------------------------------------------------------------- 
*}

lemma arbol_profundidad_respecto_num_hojas:
  assumes "es_abc profundidad n"
  shows "hojas n = 2^(profundidad n)"
using assms
by (induct n) auto

lemma lej7: "es_abc profundidad a = es_abc hojas a"
by (induct a) (auto simp add: arbol_profundidad_respecto_num_hojas)

text {*  
  --------------------------------------------------------------------- 
  Ejercicio 8. Demostrar que un árbol binario a es completo respecto del
  número de hojas syss es completo respecto del número de nodos.
  --------------------------------------------------------------------- 
*}

lemma arbol_completo_respecto_num_hojas:
  assumes "es_abc hojas n"
  shows "Suc(size n) = hojas n"
using assms
by (induct n) auto

lemma lej8: "es_abc hojas a = es_abc size a"
by (induct a) (auto simp add:arbol_completo_respecto_num_hojas [symmetric])

text {*  
  --------------------------------------------------------------------- 
  Ejercicio 9. Demostrar que un árbol binario a es completo respecto de
  la profundidad syss es completo respecto del número de nodos.
  --------------------------------------------------------------------- 
*}

lemma arbol_completo_respecto_profundidad: "es_abc profundidad n = es_abc size n"
by (simp add: lej7 lej8) 

text {*  
  --------------------------------------------------------------------- 
  Ejercicio 10. Demostrar que (abc n) es un árbol binario completo.
  --------------------------------------------------------------------- 
*}

text {*  
  --------------------------------------------------------------------- 
  Ejercicio 11. Demostrar que si a es un árbolo binario completo
  respecto de la profundidad, entonces a es igual a
  (abc (profundidad a)).
  --------------------------------------------------------------------- 
*}

text {*  
  --------------------------------------------------------------------- 
  Ejercicio 12. Encontrar una medida f tal que (es_abc f) es distinto de 
  (es_abc size).
  --------------------------------------------------------------------- 
*}

end