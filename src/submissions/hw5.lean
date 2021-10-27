import data.set

/-
CS2120 F21 HW5

The goals of this assignment are to give you
practice with proofs of propositions that use
existential quantificaton, and to develop your
understanding of formal and informal proofs in
set theory.
-/

/-
PART I: EXISTENTIAL QUANTIFICATION.
-/

/-
To start, suppose that α and β are arbitrary
types, and p and q are predicates on values
of these types: α and β, respectively.
-/

axioms 
  (α β : Type)
  (p : α → Prop)
  (q : β → Prop)

/-
In this context complete the following tasks:

(1) Write a fluent English-language statement
of the proposition to be proved. 

(2) Provide a formal proof of the proposition.

(3) Write an informal proof of the proposition.
-/

-- here's the proposition
example : 
  (∃ (f : α → β), ∀ (a : α), p a → q (f a)) →
  (∃ (a : α), p a) → 
  (∃ (b : β), q b) := 

/-
What does this propositon say? Explain it in
plain English. Here's a start: "If there's a 
function that maps/takes every α value that ... 
-- your completed English rendition here:

If there's a function that maps every α value 
such that a is a value of that type, and you 
have a proof that α implies β, then you can
proof there exists a value q of type β. Therefore,
if a value a of type α exists, then a value b
of type β exists.
-/


-- Give your formal proof here
begin
  assume h,
  cases h with f t,
  assume aex,
  apply exists.elim aex,
  assume a,
  assume pa,
  apply exists.intro,
  apply t,
  apply pa,
end
  

