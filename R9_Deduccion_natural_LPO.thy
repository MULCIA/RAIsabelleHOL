chapter {* R9: Deducción natural LPO en Isabelle/HOL *}
 
theory R9_Deduccion_natural_LPO
imports Main 
begin
 
text {*
  Demostrar o refutar los siguientes lemas usando sólo las reglas
  básicas de deducción natural de la lógica proposicional, de los
  cuantificadores y de la igualdad: 
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
*}
 
text {*
  Se usarán las reglas notnotI, mt y not_ex que demostramos a continuación.
  *}
 
lemma notnotI: "P \<Longrightarrow> \<not>\<not> P"
by auto
 
lemma mt: "\<lbrakk>F \<longrightarrow> G; \<not>G\<rbrakk> \<Longrightarrow> \<not>F"
by auto
 
lemma no_ex: "\<not>(\<exists>x. P(x)) \<Longrightarrow> \<forall>x. \<not>P(x)"
by auto
 
text {* --------------------------------------------------------------- 
  Ejercicio 1. Demostrar
       P a \<longrightarrow> (\<exists>x. Q x) \<turnstile> \<exists>x. P a \<longrightarrow> Q x 
  ------------------------------------------------------------------ *}
 
lemma ejercicio_1: 
  fixes P Q :: "'b \<Rightarrow> bool" 
  assumes "P a \<longrightarrow> (\<exists>x. Q x)"
  shows   "\<exists>x. P a \<longrightarrow> Q x"
oops
 
 
(* migtermor ferrenseg *)
lemma ejercicio_1: 
  fixes P Q :: "'b \<Rightarrow> bool" 
  assumes "P a \<longrightarrow> (\<exists>x. Q x)"
  shows   "\<exists>x. P a \<longrightarrow> Q x"
proof -
 {assume 1: "P a"
 have 2: "\<exists>x. Q x" using assms 1 by (rule mp)}
 then obtain b where 3: "Q b" by (rule exE)          
(* No sé por qué salta un aviso aquí. Aún así, sin esto no se finaliza correctamente la demostración, y con ello sí. *)
 then have 4: "(P a) \<longrightarrow> (Q b)" by (rule impI)
 then show 5: "\<exists>x. P a \<longrightarrow> Q x" by (rule exI)
qed
 
(* ivamenjim *)
(* Si se pone todo seguido, solo sale fallo en qed al final y no entiendo porqué *)
 
lemma ejercicio_1_1:  
  assumes 1: "P a \<longrightarrow> (\<exists>x. Q x)"
  shows   "\<exists>x. P a \<longrightarrow> Q x"
proof -
   assume 2: "P a"
   have 3: "(\<exists>x. Q x)" using 1 2 by (rule mp)
   obtain b where 4: "Q b" using 3 by (rule exE)
   have 5: "P a \<longrightarrow> Q b" using 4 by (rule impI)
   then have "\<exists>x. P a \<longrightarrow> Q x" by (rule exI) 
qed  
 
 
text {* --------------------------------------------------------------- 
  Ejercicio 2. Demostrar
       {\<forall>x y z. R x y \<and> R y z \<longrightarrow> R x z, 
        \<forall>x. \<not>(R x x)}
       \<turnstile> \<forall>x y. R x y \<longrightarrow> \<not>(R y x)
  ------------------------------------------------------------------ *}
 
(* migtermor ferrenseg ivamenjim marcarmor13*)
lemma ejercicio_2: 
  fixes R :: "'b \<Rightarrow> 'b \<Rightarrow> bool" 
  assumes 1: "\<forall>x y z. R x y \<and> R y z \<longrightarrow> R x z"
  assumes 2: "\<forall>x. \<not>(R x x)"
  shows   "\<forall>x y. R x y \<longrightarrow> \<not>(R y x)"
proof (rule allI)
fix x
show "\<forall>y. R x y \<longrightarrow> \<not>(R y x)" 
 proof (rule allI) 
  fix y
  {assume 3: "R x y"
   {assume 4: "R y x"
    have 5: "R x y \<and> R y x" using 3 4 by (rule conjI)
    also have 6: "\<forall> z1 z2. R x z1 \<and> R z1 z2 \<longrightarrow> R x z2" using 1 by (rule allE)
    then have 7: "\<forall> z. R x y \<and> R y z \<longrightarrow> R x z" by (rule allE)
    then have 8: "R x y \<and> R y x \<longrightarrow> R x x" by (rule allE)
    then have 9: "R x x" using 5 by (rule mp)
    have 10: "\<not>(R x x)" using 2 by (rule allE)
    then have 11: "False" using 9 by (rule notE)}
  then have 12: "\<not> (R y x)" by (rule notI)}
  thus "R x y \<longrightarrow> \<not>(R y x)" by (rule impI)
 qed
qed
 
(* ivamenjim *)
(* Semejante al anterior, pero indicando que se pruebe por la regla correspondiente *)
 
lemma ejercicio_2_1: 
  assumes 1: "\<forall>x y z. R x y \<and> R y z \<longrightarrow> R x z"
  assumes 2: "\<forall>x. \<not>(R x x)"
  shows   "\<forall>x y. R x y \<longrightarrow> \<not>(R y x)"
proof (rule allI)
fix x
show "\<forall>y. R x y \<longrightarrow> \<not>(R y x)" 
 proof (rule allI) 
  fix y
  {assume 3: "R x y"
   {assume 4: "R y x"
    have 5: "R x y \<and> R y x" using 3 4 ..
    have 6: "\<forall> y z. R x y \<and> R y z \<longrightarrow> R x z" using 1 ..
    then have 7: "\<forall> z. R x y \<and> R y z \<longrightarrow> R x z" ..
    then have 8: "R x y \<and> R y x \<longrightarrow> R x x" ..
    then have 9: "R x x" using 5 ..
    have 10: "\<not>(R x x)" using 2 ..
    then have 11: "False" using 9 ..}
  then have 12: "\<not> (R y x)" ..}
  thus "R x y \<longrightarrow> \<not>(R y x)" ..
 qed
qed 
 
text {* --------------------------------------------------------------- 
  Ejercicio 3. Demostrar o refutar
       (\<forall>x. \<exists>y. P x y) \<longrightarrow> (\<exists>y. \<forall>x. P x y)
  ------------------------------------------------------------------ *}
 
(* ivamenjim ferrenseg paupeddeg*)
lemma ejercicio_3: 
  assumes "(\<forall>x. \<exists>y. P x y)"
  shows   "(\<exists>y. \<forall>x. P x y)"
  quickcheck
oops  
 
(* Y se encuentra el contraejemplo: P = (\<lambda>x. undefined)(a1 := {a2}, a2 := {a1}) *)
 
(* migtermor *)
fun P :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "P x y = (x=y)"
 
lemma ejercicio3:
 "(\<forall>x. \<exists>y. P x y) \<longrightarrow> (\<exists>y. \<forall>x. P x y)"
quickcheck
oops
 
text {* --------------------------------------------------------------- 
  Ejercicio 4. Demostrar o refutar
     {\<forall>x. P a x x, 
      \<forall>x y z. P x y z \<longrightarrow> P (f x) y (f z)\<rbrakk>
     \<turnstile> \<exists>z. P (f a) z (f (f a))
  ------------------------------------------------------------------ *}
 
(* ferrenseg ivamenjim *)
lemma ejercicio_4:
  assumes 1:"\<forall>x. P a x x" and 2:"\<forall>x y z. P x y z \<longrightarrow> P (f x) y (f z)"
  shows "\<exists>z. P (f a) z (f (f a))"
proof -
  have 4:"P a (f a) (f a)" using 1 ..
  also have 5:"\<forall>y z. P a y z \<longrightarrow> P (f a) y (f z)" using 2 ..
  then have 6:"\<forall>z. P a (f a) z \<longrightarrow> P (f a) (f a) (f z)" ..
  then have 7:"P a (f a) (f a) \<longrightarrow> P (f a) (f a) (f (f a))" ..
  also have 8:"P (f a) (f a) (f (f a))" using 7 4 by (rule mp)
  then show "\<exists>z. P (f a) z (f (f a))" ..
qed
 
(* migtermor *)
lemma ejercicio_4_2: 
  fixes P :: "'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool" 
  assumes 1: "\<forall>x. P a x x"
  assumes 2: "\<forall>x y z.  P x y z \<longrightarrow> P (f x) y (f z)"
  shows   " \<exists>z. P (f a) z (f (f a))"
proof (rule exI)
 have 3: "P a (f a) (f a)" using 1 by (rule allE)
 have 4: "\<forall>y z.  P a y z \<longrightarrow> P (f a) y (f z)" using 2 by (rule allE)
 then have 5: "\<forall>z.  P a (f a) z \<longrightarrow> P (f a) (f a) (f z)" by (rule allE)
 then have 6: "P a (f a) (f a) \<longrightarrow> P (f a) (f a) (f (f a))" by (rule allE)
 then show "P (f a) (f a) (f (f a))" using 3 by (rule mp)
qed
 
(* paupeddeg *)
lemma ejercicio_4_3:
  assumes " \<forall>x. P a x x " 
          " \<forall>x y z. P x y z \<longrightarrow> P (f x) y (f z)"
  shows "\<exists>z. P (f a) z (f (f a))"
proof
  have "\<forall> y z. P a y z \<longrightarrow> P (f a) y (f z)" using assms(2) by (rule allE)
  hence "\<forall>z. P a (f a) z \<longrightarrow> P (f a) (f a) (f z)"  by (rule allE)
  hence "P a (f a) (f a) \<longrightarrow> P (f a) (f a) (f (f a))"  by (rule allE)
  have "P a (f a) (f a)" using assms(1) by (rule allE)
  show "P (f a) (f a) (f (f a))" using `P a (f a) (f a) \<longrightarrow> P (f a) (f a) (f (f a))` `P a (f a) (f a)`  by (rule mp)
qed
 
text {* --------------------------------------------------------------- 
  Ejercicio 5. Demostrar o refutar
     {\<forall>y. Q a y, 
      \<forall>x y. Q x y \<longrightarrow> Q (s x) (s y)} 
     \<turnstile> \<exists>z. Qa z \<and> Q z (s (s a))
  ------------------------------------------------------------------ *}
 
(* ferrenseg ivamenjim *)
lemma ejercicio_5:
  assumes 1:"\<forall>y. Q a y" and 2:"\<forall>x y. Q x y \<longrightarrow> Q (s x) (s y)"
  shows "\<exists>z. Q a z \<and> Q z (s (s a))"
proof
  have 3:"Q a (s a)" using 1 ..
  also have 4:"\<forall>y. Q a y \<longrightarrow> Q (s a) (s y)" using 2 ..
  then have 5:"Q a (s a) \<longrightarrow> Q (s a) (s (s a))" ..
  then have 6:"Q (s a) (s (s a))" using 3 by (rule mp)
  show "Q a (s a) \<and> Q (s a) (s (s a))" using 3 6 by (rule conjI)
qed
 
(* migtermor *)
lemma ejercicio_5_2: 
  fixes P :: "'b \<Rightarrow> 'b \<Rightarrow> bool" 
  assumes 1: "\<forall>y. Q a y"
  assumes 2: "\<forall>x y. Q x y \<longrightarrow> Q (s x) (s y)"
  shows   " \<exists>z. Q a z \<and> Q z (s (s a))"
proof -
 have 3: "Q a (s a)" using 1 by (rule allE)
 have 4: "\<forall>y. Q a y \<longrightarrow> Q (s a) (s y)" using 2 by (rule allE)
 then have 5: "Q a (s a) \<longrightarrow> Q (s a) (s (s a))" by (rule allE)
 then have 6: "Q (s a) (s (s a))" using 3 by (rule mp)
 have "Q a (s a) \<and> Q (s a) (s (s a))" using 3 6 by (rule conjI)
 then show "\<exists>z. Q a z \<and> Q z (s (s a))" by (rule exI)
qed
 
(* paupeddeg *)
lemma ejercicio_5_3:
  assumes "\<forall>y. Q a y" 
          "\<forall>x y. Q x y \<longrightarrow> Q (s x) (s y)"
  shows "\<exists>z. Q a z \<and> Q z (s (s a))"
proof 
have "\<forall>y. Q a y \<longrightarrow> Q (s a) (s y)" using assms(2) by (rule allE)
hence "Q a (s a) \<longrightarrow> Q (s a) (s (s a))" by (rule allE)
have "Q a (s a)" using assms(1) by (rule allE)
have "Q (s a) (s (s a))" using `Q a (s a) \<longrightarrow> Q (s a) (s (s a))` `Q a (s a)` by (rule mp)
show "Q a (s a) \<and> Q (s a) (s (s a))" using `Q a (s a)` `Q (s a) (s (s a))` by (rule conjI)
qed
 
end