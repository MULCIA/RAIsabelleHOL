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
 
text {* --------------------------------------------------------------- 
  Ejercicio 2. Demostrar
       {\<forall>x y z. R x y \<and> R y z \<longrightarrow> R x z, 
        \<forall>x. \<not>(R x x)}
       \<turnstile> \<forall>x y. R x y \<longrightarrow> \<not>(R y x)
  ------------------------------------------------------------------ *}
 
lemma ejercicio_2: 
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

text {* --------------------------------------------------------------- 
  Ejercicio 3. Demostrar o refutar
       (\<forall>x. \<exists>y. P x y) \<longrightarrow> (\<exists>y. \<forall>x. P x y)
  ------------------------------------------------------------------ *}
 
text {* --------------------------------------------------------------- 
  Ejercicio 4. Demostrar o refutar
     {\<forall>x. P a x x, 
      \<forall>x y z. P x y z \<longrightarrow> P (f x) y (f z)\<rbrakk>
     \<turnstile> \<exists>z. P (f a) z (f (f a))
  ------------------------------------------------------------------ *}
 
text {* --------------------------------------------------------------- 
  Ejercicio 5. Demostrar o refutar
     {\<forall>y. Q a y, 
      \<forall>x y. Q x y \<longrightarrow> Q (s x) (s y)} 
     \<turnstile> \<exists>z. Qa z \<and> Q z (s (s a))
  ------------------------------------------------------------------ *}
 
end