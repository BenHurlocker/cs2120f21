-- AND rules (P ∧ Q)
-- and.intro p q : combines p and q to make P ∧ Q
-- elim_left : (P ∧ Q) → P
-- elim_right : (P ∧ Q) → Q
example : ∀ (P Q : Prop), P ∧ Q → Q ∧ P :=
begin
  assume P Q,
  assume h,
  have p := h.elim_left,
  have q := h.elim_right,
  exact and.intro q p,
end

example : ∀ (P Q : Prop), P ∧ Q → Q ∧ P :=
begin
  assume P Q,
  assume h,
  apply and.intro,
end

-- OR rules (P ∨ Q)
-- or.intro_right : (P ∨ Q) → Q
-- or.intro_left : (P ∨ Q) → P
-- or.elim : (P ∨ Q) splits P and Q
-- cases x : applies or.inl and or.inr
example : ∀ (P Q : Prop), P ∨ Q → Q ∨ P :=
begin
  assume P Q,
  assume h,
  cases h with p q,
  apply or.intro_right,
  exact p,
  apply or.inl,
  exact q,
end

example : ∀ (P Q : Prop), P ∨ Q → Q ∨ P :=
begin
  assume P Q,
  assume h,
  apply or.elim h,
  assume p,
  apply or.inr p,

  assume q,
  apply or.inl q,
end

-- false rules

example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume p,
  assume np,
  have f := np p,
  exact f,
end

theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume h,
  have pornp := classical.em P,
  cases pornp with p np,
  
  exact p,
  have f := h np,
  apply false.elim,
  exact f,
end


axioms
  (Person : Type)
  (Likes : Person → Person → Prop)

example :
¬ (∀ p : Person, Likes p p) ↔
∃ p : Person, ¬ Likes p p :=
begin
  apply iff.intro _ _,
  -- forward
    assume h,
    have f := classical.em (∃ (p : Person), ¬Likes p p),
    cases f,
  -- case #1
    exact f,
  -- case #2: propose new fact, proof to be constructed in this contradiction
    have contra : ∀ (p : Person), Likes p p := _,
    contradiction,

    assume p,
    have g := classical.em (Likes p p),
    cases g,
    exact g,

    have a : ∃ (p : Person), ¬Likes p p := exists.intro p g,
    contradiction,
  -- backward
    assume h,
end 