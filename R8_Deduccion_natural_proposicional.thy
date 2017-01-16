chapter {* R8: Deducción natural proposicional en Isabelle/HOL *}
 
theory R8_Deduccion_natural_proposicional
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
     \<not>q \<longrightarrow> \<not>p \<turnstile> p \<longrightarrow> q
  ------------------------------------------------------------------ *}
 
lemma ejercicio_1:
  assumes 1: "\<not>q \<longrightarrow> \<not>p"
  shows "p \<longrightarrow> q"
proof -
  {assume 2: "p"
   then have 3: "\<not>\<not>p" by (rule notnotI)
   have 4: "\<not>\<not>q" using 1 3 by (rule mt)
   then have 5: "q" by (rule notnotD)} 
  then show "p \<longrightarrow> q" by (rule impI)
qed

lemma ejercicio_1_2:
  assumes "\<not>q \<longrightarrow> \<not>p"
          "p"
  shows "p \<longrightarrow> q"
using assms
by auto

text {* --------------------------------------------------------------- 
  Ejercicio 2. Demostrar
     \<not>(\<not>p \<and> \<not>q) \<turnstile> p \<or> q
  ------------------------------------------------------------------ *}

lemma ejercicio_2:
  assumes 1: "\<not>(\<not>p \<and> \<not>q)"
  shows "p \<or> q"
proof -
  {assume 2: "(\<not>p \<and> \<not>q)"
   have 3: "p" using 1 2 by (rule notE)
   then have 4: "p \<or> q" by (rule disjI1)}
   then show "p \<or> q" by auto
qed

lemma ejercicio_2_2:
  assumes "\<not>(\<not>p \<and> \<not>q)" and
          "(\<not>p \<and> \<not>q)"
  shows "p \<or> q"
using assms
by auto


text {* --------------------------------------------------------------- 
  Ejercicio 3. Demostrar
     \<not>(\<not>p \<or> \<not>q) \<turnstile> p \<and> q
  ------------------------------------------------------------------ *}

text {* --------------------------------------------------------------- 
  Ejercicio 4. Demostrar
     \<not>(p \<and> q) \<turnstile> \<not>p \<or> \<not>q
  ------------------------------------------------------------------ *}
 
text {* --------------------------------------------------------------- 
  Ejercicio 5. Demostrar
     \<turnstile> (p \<longrightarrow> q) \<or> (q \<longrightarrow> p)
  ------------------------------------------------------------------ *}
 
end