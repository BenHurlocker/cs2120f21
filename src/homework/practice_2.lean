/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro

example : false := _    -- trick question? why? 
-- There is no proof of false

-- P or P implies P
example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
  assume P, 
  apply iff.intro _ _,
  -- forward
  assume porp,
  apply or.elim porp,
  -- left disjunct is true
    assume p,
    exact p,
  -- right disjunct is true
    assume p,
    exact p,
  -- backwards
  assume p,
  apply or.intro_left P p,
end

-- P and P implies P
example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  assume h,
  apply and.elim_left h,
  assume h,
  apply and.intro h h,
end

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  assume h,
  apply or.elim h,
  assume p,
  apply or.intro_right,
  exact p,
  assume q,
  apply or.intro_left,
  exact q,
  assume h,
  apply or.elim h,
  assume q,
  apply or.intro_right,
  exact q,
  assume p,
  apply or.intro_left,
  exact p,
end

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  assume h,
  have q := h.right,
  have p := h.left,
  apply and.intro q p,
  assume h,
  have q := h.left,
  have p := h.right,
  apply and.intro p q,
end

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
  {
    assume h,
    apply or.intro_left,
    have p := h.elim_left,
    have qorr := h.elim_right,
    apply or.elim qorr,
    assume q,
    apply and.intro p q,
    
    assume r,
    apply and.intro,

  },
end

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
  {
    assume h,
    apply and.intro,
    apply or.elim h,
    assume p,
    apply or.intro_left,
    exact p,
    assume qorr,
    have q := qorr.elim_left,
    apply or.intro_right,
    exact q,
    apply or.elim h,
    assume p,
    apply or.intro_left,
    exact p,
    assume qorr,
    have r := qorr.elim_right,
    apply or.intro_right,
    exact r,
  },
  {
    assume h,
    have porq := h.elim_left,
    have porr := h.elim_right, 
    apply or.elim porq,
    assume p,
    apply or.intro_left,
    exact p,

    assume q,
    apply or.elim porr,
    assume p,
    apply or.intro_left,
    exact p,

    assume r,
    apply or.intro_right,
    apply and.intro q r,
  }
  
end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  {
  assume h,
  have p := h.elim_left,
  apply p,
  },
  {
  assume p,
  apply and.intro _ _,
  apply p,
  apply or.intro_left,
  exact p,
  }


end

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  {
  assume h,
  apply or.elim h,
  assume p,
  apply p,
  assume pandq,
  have p := pandq.elim_left,
  exact p,
  },
  {
  assume p,
  apply or.intro_left,
  exact p,
  }
end

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  apply iff.intro _ _,
  assume h,
  exact true.intro,

  assume t,
  apply or.intro_right,
  exact true.intro,
end

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  
  assume h,
  apply or.elim h,
  assume p,
  exact p,
  apply false.elim,

  assume p,
  apply or.intro_left,
  exact p,
end

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  assume h,
  have p := h.left,
  exact p,
  
  assume p,
  apply and.intro p true.intro,
end

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro _ _,
  {
    assume h,
    have f := h.elim_right,
    exact f,
  },
  {
    assume f,
    apply false.elim,
    exact f,
  }
end


