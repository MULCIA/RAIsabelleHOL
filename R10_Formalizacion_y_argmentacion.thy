chapter {* R10: Formalización y argumentación con Isabelle/HOL *}

theory R10_Formalizacion_y_argmentacion
imports Main 
begin

text {*
  --------------------------------------------------------------------- 
  El objetivo de esta es relación formalizar y demostrar la corrección
  de los argumentos automáticamente y detalladamente usando sólo las reglas
  básicas de deducción natural. 

  · conjI:      \<lbrakk>P; Q\<rbrakk> \<Longrightarrow> P \<and> Q
  · conjunct1:  P \<and> Q \<Longrightarrow> P
  · conjunct2:  P \<and> Q \<Longrightarrow> Q  
  · notnotD:    \<not>\<not> P \<Longrightarrow> P
  · mp:         \<lbrakk>P \<longrightarrow> Q; P\<rbrakk> \<Longrightarrow> Q 
  · impI:       (P \<Longrightarrow> Q) \<Longrightarrow> P \<longrightarrow> Q
  · disjI1:     P \<Longrightarrow> P \<or> Q
  · disjI2:     Q \<Longrightarrow> P \<or> Q
  · disjE:      \<lbrakk>P \<or> Q; P \<Longrightarrow> R; Q \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R 
  · FalseE:     False \<Longrightarrow> P
  · notE:       \<lbrakk>\<not>P; P\<rbrakk> \<Longrightarrow> R
  · notI:       (P \<Longrightarrow> False) \<Longrightarrow> \<not>P
  · iffI:       \<lbrakk>P \<Longrightarrow> Q; Q \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P = Q
  · iffD1:      \<lbrakk>Q = P; Q\<rbrakk> \<Longrightarrow> P 
  · iffD2:      \<lbrakk>P = Q; Q\<rbrakk> \<Longrightarrow> P
  · ccontr:     (\<not>P \<Longrightarrow> False) \<Longrightarrow> P

  · allI:       \<lbrakk>\<forall>x. P x; P x \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R
  · allE:       (\<And>x. P x) \<Longrightarrow> \<forall>x. P x
  · exI:        P x \<Longrightarrow> \<exists>x. P x
  · exE:        \<lbrakk>\<exists>x. P x; \<And>x. P x \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q

  · refl:       t = t
  · subst:      \<lbrakk>s = t; P s\<rbrakk> \<Longrightarrow> P t
  · trans:      \<lbrakk>r = s; s = t\<rbrakk> \<Longrightarrow> r = t
  · sym:        s = t \<Longrightarrow> t = s
  · not_sym:    t \<noteq> s \<Longrightarrow> s \<noteq> t
  · ssubst:     \<lbrakk>t = s; P s\<rbrakk> \<Longrightarrow> P t
  · box_equals: \<lbrakk>a = b; a = c; b = d\<rbrakk> \<Longrightarrow> a: = d
  · arg_cong:   x = y \<Longrightarrow> f x = f y
  · fun_cong:   f = g \<Longrightarrow> f x = g x
  · cong:       \<lbrakk>f = g; x = y\<rbrakk> \<Longrightarrow> f x = g y
  --------------------------------------------------------------------- 
*}

text {*
  Se usarán las reglas notnotI, mt, no_ex y no_para_todo que demostramos
  a continuación. 
  *}

lemma notnotI: "P \<Longrightarrow> \<not>\<not> P"
by auto

lemma mt: "\<lbrakk>F \<longrightarrow> G; \<not>G\<rbrakk> \<Longrightarrow> \<not>F"
by auto

lemma no_ex: "\<not>(\<exists>x. P(x)) \<Longrightarrow> \<forall>x. \<not>P(x)"
by auto

lemma no_para_todo: "\<not>(\<forall>x. P(x)) \<Longrightarrow> \<exists>x. \<not>P(x)"
by auto

text {* --------------------------------------------------------------- 
  Ejercicio 1. Formalizar, y demostrar la corrección, del siguiente
  argumento 
     Si la válvula está abierta o la monitorización está preparada,
     entonces se envía una señal de reconocimiento y un mensaje de
     funcionamiento al controlador del ordenador. Si se envía un mensaje 
     de funcionamiento al controlador del ordenador o el sistema está en 
     estado normal, entonces se aceptan las órdenes del operador. Por lo
     tanto, si la válvula está abierta, entonces se aceptan las órdenes
     del operador. 
  Usar A : La válvula está abierta.
       P : La monitorización está preparada.
       R : Envía una señal de reconocimiento.
       F : Envía un mensaje de funcionamiento.
       N : El sistema está en estado normal.
       O : Se aceptan órdenes del operador.
  ------------------------------------------------------------------ *}

lemma ejer_1:
  assumes 1: "A \<or> P \<longrightarrow> R \<and> F" 
  assumes 2: "F \<or> N \<longrightarrow> OK"
  shows "A \<longrightarrow> OK"
proof -
  {assume 3: "A"
   have 4: "A \<or> P" using 3 by (rule disjI1)
   have 5: "R \<and> F" using 1 4 by (rule mp)
   have 6: "F" using 5 by (rule conjunct2)
   have 7: "F \<or> N" using 6 by (rule disjI1)
   have 8: "OK" using 2 7 by (rule mp)}
  then show "A \<longrightarrow> OK" by (rule impI)
qed  

text {* --------------------------------------------------------------- 
  Ejercicio 2. Formalizar, y decidir la corrección, del siguiente
  argumento 
     Hay estudiantes inteligentes y hay estudiantes trabajadores. Por
     tanto, hay estudiantes inteligentes y trabajadores.
  Usar I(x) para x es inteligente
       T(x) para x es trabajador
  ------------------------------------------------------------------ *}

lemma ejer_2:
  assumes "(\<exists>x. I(x)) \<and> (\<exists>x. T(x))"
  shows   "\<exists>x. (I(x) \<and> T(x))"
  quickcheck
oops

text {* --------------------------------------------------------------- 
  Ejercicio 3. Formalizar, y decidir la corrección, del siguiente
  argumento 
     Los hermanos tienen el mismo padre. Juan es hermano de Luis. Carlos
     es padre de Luis. Por tanto, Carlos es padre de Juan.
  Usar H(x,y) para x es hermano de y
       P(x,y) para x es padre de y
       j      para Juan
       l      para Luis
       c      para Carlos
  ------------------------------------------------------------------ *}

lemma ejer_3:
  assumes 1: "\<forall>x y. P(x,y) \<longrightarrow> (\<forall>z. (H(z,y) \<longrightarrow> P(x,z)))" 
  assumes 2: "H(j,l)"
  assumes 3: "P(c,l)"
  shows "P(c,j)"
proof -
  have 4 : "\<forall>y. P(c,y) \<longrightarrow> (\<forall>z. (H(z,y) \<longrightarrow> P(c,z)))" using 1 by (rule allE)
  have 5 : "P(c,l) \<longrightarrow> (\<forall>z. (H(z,l) \<longrightarrow> P(c,z)))" using 4 by (rule allE)
  then have 6 : "(\<forall>z. (H(z,l) \<longrightarrow> P(c,z)))" using 3 by (rule mp)
  have 7 : "H(j,l) \<longrightarrow> P(c,j)" using 6 by (rule allE)
  then show "P(c,j)" using 2 by (rule mp)
qed 

text {* --------------------------------------------------------------- 
  Ejercicio 4. Formalizar, y decidir la corrección, del siguiente
  argumento 
     Los aficionados al fútbol aplauden a cualquier futbolista
     extranjero. Juanito no aplaude a futbolistas extranjeros. Por
     tanto, si hay algún futbolista extranjero nacionalizado español,
     Juanito no es aficionado al fútbol.
  Usar Af(x)   para x es aficicionado al fútbol
       Ap(x,y) para x aplaude a y
       E(x)    para x es un futbolista extranjero
       N(x)    para x es un futbolista nacionalizado español
       j       para Juanito
  ------------------------------------------------------------------ *}

lemma ejer_4:
  assumes 1: "\<forall>x y. Af(x) \<and> E(y) \<longrightarrow> Ap(x,y)"
  assumes 2: "\<not>(\<exists>x. E(x) \<and> Ap(j,x))"
  shows "(\<exists>x. E(x) \<and> N(x)) \<longrightarrow> \<not>Af(j)"  
  proof (rule impI)
  assume 3: "\<exists>x. E(x) \<and> N(x)"
    then obtain a where 4: "E(a) \<and> N(a)" by (rule exE)
    then have 5: "E(a)" by (rule conjunct1)
    show 6: "\<not>Af(j)"
    proof (rule notI)
      assume 7: "Af(j)"
      then have 8: "Af(j) \<and> E(a)" using 5 by (rule conjI)
      have 9: "\<forall>y. Af(j) \<and> E(y) \<longrightarrow> Ap(j,y)" using 1 by (rule allE)
      have 10: "Af(j) \<and> E(a) \<longrightarrow> Ap(j,a)" using 9 by (rule allE)
      have 11: "Ap(j,a)" using 10 8 by (rule mp)
      have 12: "E(a) \<and> Ap(j,a)" using 5 11 by (rule conjI)
      have 13: "\<exists>x. E(x) \<and> Ap(j,x)" using 12 by (rule exI)
      show "False" using 2 13 by (rule notE)
    qed
qed  

text {* --------------------------------------------------------------- 
  Ejercicio 5. Formalizar, y decidir la corrección, del siguiente
  argumento 
     El esposo de la hermana de Toni es Roberto. La hermana de Toni es
     María. Por tanto, el esposo de María es Roberto. 
  Usar e(x) para el esposo de x
       h    para la hermana de Toni
       m    para María
       r    para Roberto
  ------------------------------------------------------------------ *}

lemma ejer_5:
  assumes 1: "e(h) = r"
  assumes 2: "h = m"
  shows   "e(m) = r"
  proof -
    show "e(m) = r" using 2 1 by (rule subst)
qed

end