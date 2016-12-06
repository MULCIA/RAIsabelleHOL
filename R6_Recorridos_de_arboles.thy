chapter {* R6: Recorridos de árboles *}

theory R6_Recorridos_de_arboles
imports Main 
begin 

text {*  
  --------------------------------------------------------------------- 
  Ejercicio 1. Definir el tipo de datos arbol para representar los
  árboles binarios que tiene información en los nodos y en las hojas. 
  Por ejemplo, el árbol
          e
         / \
        /   \
       c     g
      / \   / \
     a   d f   h 
  se representa por "N e (N c (H a) (H d)) (N g (H f) (H h))".
  --------------------------------------------------------------------- 
*}

datatype 'a arbol = H "'a" | N "'a" "'a arbol" "'a arbol"

value "N e (N c (H a) (H d)) (N g (H f) (H h))" 

text {*  
  --------------------------------------------------------------------- 
  Ejercicio 2. Definir la función 
     preOrden :: "'a arbol \<Rightarrow> 'a list"
  tal que (preOrden a) es el recorrido pre orden del árbol a. Por
  ejemplo, 
     preOrden (N e (N c (H a) (H d)) (N g (H f) (H h)))
     = [e,c,a,d,g,f,h] 
  --------------------------------------------------------------------- 
*}

fun preOrden :: "'a arbol \<Rightarrow> 'a list" where
  "preOrden (H t) = [t]"
| "preOrden (N t i d) = [t] @ (preOrden i) @ (preOrden d)"

value "preOrden (N e (N c (H a) (H d)) (N g (H f) (H h)))  
      = [e,c,a,d,g,f,h]" 

text {*  
  --------------------------------------------------------------------- 
  Ejercicio 3. Definir la función 
     postOrden :: "'a arbol \<Rightarrow> 'a list"
  tal que (postOrden a) es el recorrido post orden del árbol a. Por
  ejemplo, 
     postOrden (N e (N c (H a) (H d)) (N g (H f) (H h)))
     = [e,c,a,d,g,f,h] 
  --------------------------------------------------------------------- 
*}

fun postOrden :: "'a arbol \<Rightarrow> 'a list" where
  "postOrden (H t) = [t]"
| "postOrden (N t i d) = (postOrden i) @ (postOrden d) @ [t]"

value "postOrden (N e (N c (H a) (H d)) (N g (H f) (H h)))
       = [a,d,c,f,h,g,e]"

text {*  
  --------------------------------------------------------------------- 
  Ejercicio 4. Definir la función 
     inOrden :: "'a arbol \<Rightarrow> 'a list"
  tal que (inOrden a) es el recorrido in orden del árbol a. Por
  ejemplo, 
     inOrden (N e (N c (H a) (H d)) (N g (H f) (H h)))
     = [a,c,d,e,f,g,h]
  --------------------------------------------------------------------- 
*}

fun inOrden :: "'a arbol \<Rightarrow> 'a list" where
  "inOrden (H t) = [t]"
| "inOrden (N t i d) = (inOrden i) @ [t] @ (inOrden d)"

value "inOrden (N e (N c (H a) (H d)) (N g (H f) (H h)))
       = [a,c,d,e,f,g,h]"

text {*  
  --------------------------------------------------------------------- 
  Ejercicio 5. Definir la función 
     espejo :: "'a arbol \<Rightarrow> 'a arbol"
  tal que (espejo a) es la imagen especular del árbol a. Por ejemplo, 
     espejo (N e (N c (H a) (H d)) (N g (H f) (H h)))
     = N e (N g (H h) (H f)) (N c (H d) (H a))
  --------------------------------------------------------------------- 
*}

fun espejo :: "'a arbol \<Rightarrow> 'a arbol" where
  "espejo (H t) = H t"
| "espejo (N t i d) = N t (espejo d) (espejo i)"

value "espejo (N e (N c (H a) (H d)) (N g (H f) (H h))) 
       = N e (N g (H h) (H f)) (N c (H d) (H a))"

text {*  
  --------------------------------------------------------------------- 
  Ejercicio 6. Demostrar que
     preOrden (espejo a) = rev (postOrden a)
  --------------------------------------------------------------------- 
*}

lemma  "preOrden (espejo a) = rev (postOrden a)" (is "?P a")
proof (induct a)
  fix x 
  show "?P (H x)" by simp 
next
  fix x 
  fix i assume h1: "?P i"
  fix d assume h2: "?P d"
  have "preOrden (espejo (N x i d)) = preOrden (N x (espejo d) (espejo i))" by simp
  also have "... = [x] @ (preOrden (espejo d)) @ (preOrden (espejo i))" by simp
  also have "... = [x] @ rev (postOrden d) @ rev (postOrden i)" using h1 h2 by simp 
  finally show "preOrden (espejo (N x i d)) = rev (postOrden (N x i d))" by simp
qed

text {*  
  --------------------------------------------------------------------- 
  Ejercicio 7. Demostrar que
     postOrden (espejo a) = rev (preOrden a)
  --------------------------------------------------------------------- 
*}

lemma "postOrden (espejo a) = rev (preOrden a)"
oops

text {*  
  --------------------------------------------------------------------- 
  Ejercicio 8. Demostrar que
     inOrden (espejo a) = rev (inOrden a)
  --------------------------------------------------------------------- 
*}

theorem "inOrden (espejo a) = rev (inOrden a)"
oops

text {*  
  --------------------------------------------------------------------- 
  Ejercicio 9. Definir la función 
     raiz :: "'a arbol \<Rightarrow> 'a"
  tal que (raiz a) es la raiz del árbol a. Por ejemplo, 
     raiz (N e (N c (H a) (H d)) (N g (H f) (H h))) = e
  --------------------------------------------------------------------- 
*}

fun raiz :: "'a arbol \<Rightarrow> 'a" where
  "raiz t = undefined"

value "raiz (N e (N c (H a) (H d)) (N g (H f) (H h))) = e"

text {*  
  --------------------------------------------------------------------- 
  Ejercicio 10. Definir la función 
     extremo_izquierda :: "'a arbol \<Rightarrow> 'a"
  tal que (extremo_izquierda a) es el nodo más a la izquierda del árbol
  a. Por ejemplo,  
     extremo_izquierda (N e (N c (H a) (H d)) (N g (H f) (H h))) = a
  --------------------------------------------------------------------- 
*}

fun extremo_izquierda :: "'a arbol \<Rightarrow> 'a" where
  "extremo_izquierda t = undefined"

value "extremo_izquierda (N e (N c (H a) (H d)) (N g (H f) (H h))) = a"

text {*  
  --------------------------------------------------------------------- 
  Ejercicio 11. Definir la función 
     extremo_derecha :: "'a arbol \<Rightarrow> 'a"
  tal que (extremo_derecha a) es el nodo más a la derecha del árbol
  a. Por ejemplo,  
     extremo_derecha (N e (N c (H a) (H d)) (N g (H f) (H h))) = h
  --------------------------------------------------------------------- 
*}

fun extremo_derecha :: "'a arbol \<Rightarrow> 'a" where
  "extremo_derecha t = undefined"

value "extremo_derecha (N e (N c (H a) (H d)) (N g (H f) (H h))) = h"

text {*  
  --------------------------------------------------------------------- 
  Ejercicio 12. Demostrar o refutar
     last (inOrden a) = extremo_derecha a
  --------------------------------------------------------------------- 
*}

theorem "last (inOrden a) = extremo_derecha a"
oops

text {*  
  --------------------------------------------------------------------- 
  Ejercicio 13. Demostrar o refutar
     hd (inOrden a) = extremo_izquierda a
  --------------------------------------------------------------------- 
*}

theorem "hd (inOrden a) = extremo_izquierda a"
oops

text {*  
  --------------------------------------------------------------------- 
  Ejercicio 14. Demostrar o refutar
     hd (preOrden a) = last (postOrden a)
  --------------------------------------------------------------------- 
*}

theorem "hd (preOrden a) = last (postOrden a)"
oops

text {*  
  --------------------------------------------------------------------- 
  Ejercicio 15. Demostrar o refutar
     hd (preOrden a) = raiz a
  --------------------------------------------------------------------- 
*}

theorem "hd (preOrden a) = raiz a"
oops

text {*  
  --------------------------------------------------------------------- 
  Ejercicio 16. Demostrar o refutar
     hd (inOrden a) = raiz a
  --------------------------------------------------------------------- 
*}

theorem "hd (inOrden a) = raiz a"
oops

text {*  
  --------------------------------------------------------------------- 
  Ejercicio 17. Demostrar o refutar
     last (postOrden a) = raiz a
  --------------------------------------------------------------------- 
*}

theorem "last (postOrden a) = raiz a"
oops

end