import algebra.algebra.basic tactic.ring
/-
Read, understand (collaborating if necessary) the material
in chapter 17 of Jeremy Avigad's *Logic and Proof.* It's here:
https://leanprover.github.io/logic_and_proof/the_natural_numbers_and_induction.html
-/

/-
The following problems are listed in the Problems section of 
the chapter. 

#1. Solve probem #1, first sentence only.
    for any natural number n, whenever P holds of every 
    number less than n, it also holds of n. Then P holds 
    of every natural number.
#2. Solve at least one of #2 and #3. Give
    detailed but informal proofs.

    We are given a value n such that it has the property P. We are
    trying to prove that the sum off successive square numbers is equal
    to 1/6 n * (1 + n) * (1 + 2n).

    You begin by proving the case of 0 which gives you
    0^2 = 1/6(0)(1 + 0)(1 + 2(0))
    0 = 0

    Then its successor
    0^2 + 1^2 = 1/6(1)(1 + 1) (1 + 2(1))
    1 = 1

    By proving this we can say

    0^2 + 1^2 + 2^2... n^2 = 1/6(n)(1 + n)(1 + 2n)
-/

/-
To test out of the final exam ...

#1: Give a formal proof for #2 or #3.
-/

def sum_sq_to : ℕ → ℕ
|  (nat.zero) := (nat.zero)
|  (nat.succ n') := (sum_sq_to (n')) + n'.succ * n'.succ

def P : ℕ → Prop :=
 λ n , 6 * sum_sq_to n = n * (n + 1) * (2 * n + 1)

def conjecture := ∀ n, P n

def sum_sq : conjecture :=
begin
    unfold conjecture,
    assume n,
    unfold P,
    induction n with n' ih',
    ring,
    simp [sum_sq_to],
    rw mul_add,
    rw ih',
    rw nat.succ_eq_add_one,
    ring,
end

/-
#2: Formal or detailed informal proofs 10-13

10: Give an informal but detailed proof that for 
every natural number n, 1⋅n=n, using a proof by induction, 
the definition of multiplication, and the theorems proved in 
Section 17.4.

Your given n * 1 = n and you are trying to prove that n = 0.
This is done by showing that 0 * 1 = 0. You must consider all
successors of zero after doing this such that (n * 1') = (n * 1) + n.
In addition you have n' * 1 = (n * 1)'. With these we have a proof
that ∀ (n : ℕ), n * 1 = n

11: Show that multiplication distributes over addition. In other words, 
prove that for natural numbers m, n, and k, m(n+k)=mn+mk. You should use 
the definitions of addition and multiplication and facts proved in 
Section 17.4 (but nothing more).

We are given that m*( n + k) = m * k + m * n and we are trying to prove
that m = 0. This is done by showing that 0 * (n + k) = 0 * n + 0 * k. We
know that n * 0 = 0 meaning we can say that 0 * n and 0 * k are equal to 0.
Therefore we can say that 0 + 0 = 0 which the property hold for 0. We also
must consider the successors of 0.

-/
example : ∀ (m n k : ℕ), m * (n + k) = m * k + m * n :=
begin
    assume k m n,
    cases k,
    ring, 
    ring,
end
/-
12: Prove the multiplication is associative, in the same way. You can use any 
of the facts proved in Section 17.4 and the previous exercise.
-/
example : ∀ (m n k : ℕ), m * (n * k) = (m * n) * k:=
begin
    assume m n k,
    cases k,
    ring,
    ring,
end

/-
13 : Prove that multiplication is commutative.
-/

example : ∀ (m n : ℕ), m * n = n * m :=
begin
    assume m n,
    cases m,
    ring,
    ring,
end

#3 (Extra Credit): #5 or #9

NOT FINALIZED. ADVISORY. 
-/