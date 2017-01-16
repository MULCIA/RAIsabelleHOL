chapter {* R8: Deducción natural proposicional en Isabelle/HOL *}
 
theory R8_Deduccion_natural_proposicional
imports Main 
begin
 
text {*
  Demostrar o refutar los siguientes lemas usando sólo las reglas
  básicas de deducción natural de la lógica proposicional, de los
  cuantificadores y de la igualdad: 
  · conjI:      ⟦P; Q⟧ ⟹ P ∧ Q
  · conjunct1:  P ∧ Q ⟹ P
  · conjunct2:  P ∧ Q ⟹ Q  
  · notnotD:    ¬¬ P ⟹ P
  · mp:         ⟦P ⟶ Q; P⟧ ⟹ Q 
  · impI:       (P ⟹ Q) ⟹ P ⟶ Q
  · disjI1:     P ⟹ P ∨ Q
  · disjI2:     Q ⟹ P ∨ Q
  · disjE:      ⟦P ∨ Q; P ⟹ R; Q ⟹ R⟧ ⟹ R 
  · FalseE:     False ⟹ P
  · notE:       ⟦¬P; P⟧ ⟹ R
  · notI:       (P ⟹ False) ⟹ ¬P
  · iffI:       ⟦P ⟹ Q; Q ⟹ P⟧ ⟹ P = Q
  · iffD1:      ⟦Q = P; Q⟧ ⟹ P 
  · iffD2:      ⟦P = Q; Q⟧ ⟹ P
  · ccontr:     (¬P ⟹ False) ⟹ P
 
  · allI:       ⟦∀x. P x; P x ⟹ R⟧ ⟹ R
  · allE:       (⋀x. P x) ⟹ ∀x. P x
  · exI:        P x ⟹ ∃x. P x
  · exE:        ⟦∃x. P x; ⋀x. P x ⟹ Q⟧ ⟹ Q
 
  · refl:       t = t
  · subst:      ⟦s = t; P s⟧ ⟹ P t
  · trans:      ⟦r = s; s = t⟧ ⟹ r = t
  · sym:        s = t ⟹ t = s
  · not_sym:    t ≠ s ⟹ s ≠ t
  · ssubst:     ⟦t = s; P s⟧ ⟹ P t
  · box_equals: ⟦a = b; a = c; b = d⟧ ⟹ a: = d
  · arg_cong:   x = y ⟹ f x = f y
  · fun_cong:   f = g ⟹ f x = g x
  · cong:       ⟦f = g; x = y⟧ ⟹ f x = g y
*}
 
text {*
  Se usarán las reglas notnotI, mt y not_ex que demostramos a continuación.
  *}
 
lemma notnotI: "P ⟹ ¬¬ P"
by auto
 
lemma mt: "⟦F ⟶ G; ¬G⟧ ⟹ ¬F"
by auto
 
lemma no_ex: "¬(∃x. P(x)) ⟹ ∀x. ¬P(x)"
by auto
 
text {* --------------------------------------------------------------- 
  Ejercicio 1. Demostrar
     ¬q ⟶ ¬p ⊢ p ⟶ q
  ------------------------------------------------------------------ *}
 
text {* --------------------------------------------------------------- 
  Ejercicio 2. Demostrar
     ¬(¬p ∧ ¬q) ⊢ p ∨ q
  ------------------------------------------------------------------ *}
 
text {* --------------------------------------------------------------- 
  Ejercicio 3. Demostrar
     ¬(¬p ∨ ¬q) ⊢ p ∧ q
  ------------------------------------------------------------------ *}
 
text {* --------------------------------------------------------------- 
  Ejercicio 4. Demostrar
     ¬(p ∧ q) ⊢ ¬p ∨ ¬q
  ------------------------------------------------------------------ *}
 
text {* --------------------------------------------------------------- 
  Ejercicio 5. Demostrar
     ⊢ (p ⟶ q) ∨ (q ⟶ p)
  ------------------------------------------------------------------ *}
 
end