namespace implies

axioms (P Q: Prop) 

def if_p_is_true_then_so_is_Q : Prop := P → Q 

axiom p : P

-- assume P is true
-- assume we have a proof of P (p)

axiom pq : P → Q
-- assume we have a proof, pq, of P → Q

-- introduction rules for implies: assume premise, show conclusion
-- elimination rule for implies: apply a proof of P → Q to a proof of p to show Q is true

#check pq
#check p
#check (pq p)

/-
Suppose P and Q are propositions and you 
know that P → Q and that P are both true.
Show that Q is true. 

Proof: Aplly the truth of P → Q to the
truth of P to derive the truth of Q.

Proof: By the elimination rule for → with
pq aaplied to p.

proof: By "modus ponens". QED
-/
end implies

/-
FORALL
-/
namespace all

axioms 
  (T : Type)
  (P : T → Prop)
  (t: T)
  (a : ∀ (x : T), P x)


-- Does t have property P
example : P t := a t

#check a t

end all

