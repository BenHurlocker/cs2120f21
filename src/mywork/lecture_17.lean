import data.set

/-
We formally define two predicates on
natural numbers.
-/
def ev (n : ℕ) : Prop := n % 2 = 0
def od (n : ℕ) : Prop := ¬ ev n


/-
We now formally represent some sets.
Bear in mind that we represent a set
as a predicate, applicable to a value
of the member type, and "reducing to"
a proposition, possibly "about" that
value.

⋆ A set is defined by its membership
predicate. ⋆
-/
def one_to_four : set ℕ := { 1, 2, 3, 4 }

def empte : set ℕ := { n : ℕ | false }

def complete : set ℕ := { n : ℕ | true }

def evens : set ℕ := { n : ℕ | ev n }

def ods : set ℕ := { n : ℕ | od n }

def evens_union_ods : set ℕ := { n : ℕ | ev n ∨ od n }
--the set of elements that are in s1 or s2. 

def evens_intersect_ods : set ℕ  := { n : ℕ | ev n ∧ od n }

--the set of elements that are in s1 and s2.

def evens_complement : set ℕ := { n : ℕ | ¬ ev n }

def ods_complement : set ℕ := { n : ℕ | ¬ od n }

def evens_intersect_empty : set ℕ := { n : ℕ | ev n ∧ n ∈ empte}
-- n is even and n is in the empty set (no evens)

def evens_intersect_complete : set ℕ := { n : ℕ | ev n ∧ true}
-- n is even and n is in the complete set (all evens)

def evens_union_empty : set ℕ := { n : ℕ | ev n ∨ n ∈ empte}

def evens_union_complete : set ℕ := { n : ℕ | ev n ∨ n ∈ complete}

-- fill in additional interesting combinations


/-
SET THEORY NOTATIONS
-/
/- empty set

Sometimes people use ∅ to represent the empty set
-/

#check ( ∅ : set ℕ )

/- set membership

A membership predicate applied to a value
yields a proposition: one that is true for
values in the set. The ∈ notation is just 
a shorthand for application of a membership
predicate to a value, but it gives a sense
of "inclusion" of a value in a collection
of values.

ev n (is the same as) n ∈ ev

-/
#check evens 0
#check 0 ∈ evens
#check 1 ∈ evens

/- set difference

The difference between sets s1 and s2, 
written s1 \ s2, is the set of values
that are in s1 but not in s2. You can
think of this as the set s1 with the
elements in s2 "taken away." Sometimes
people use subtraction notation for
set difference: s1 - s2.

if s1 is 1, 2, 3, 4,
and s2 is 1, 3, 5
then s1 - s2 = 2, 4
-/
#check evens \ ods -- evens
#check evens \ evens -- empty
#check evens \ empte -- evens
#check evens \ complete -- empty


/- complement

The complement of a set s is the set of all
values in the "universe of discourse" (in Lean,
a type) that are not in s. Lean doesn't provide
a notation, so we have to define it ourselves.
Here we define compl as the complement of a 
set of natural numbers.
-/

def compl_nat (s : set ℕ ) : set ℕ :=
{a | a ∉ s}
-- all values a, such that a is not in s (all ℕ)

#check compl_nat evens -- compliment of evens = odds

/- union
The union of two sets, s1 and s2, written
as s1 ∪ s2, is the set of elements that are 
in s1 or s2. 
-/

#check ods ∪ complete -- complete set
#check ods ∪ empte -- odds
#check ods ∪ evens -- complete set


/- intersection 

The intersection of two sets, s1 and s2, written
as s1 ∩ s2, is the set of elements that are in s1
and in s2.

-/

#check ods ∩ empte -- empty
#check evens ∩ complete -- evens
#check ods ∩ evens -- empty

/- product 

s1 : 1 2 3
s2 : 4 5 6
- product of two sets are their ordered pairs (9 in this case)

The product of two sets, (s1 : set T) and
(s2 : set V) is the set of all pairs (t, v),
where t ∈ s1 and v ∈ t2. People sometimes
use × to represent the set product operation.
In Lean we have to define it ourselves.
-/

def prodset {T V : Type} (s1 : set T) (s2 : set V) := 
  { pr : T × V | pr.1 ∈ s1 ∧ pr.2 ∈ s2 }

#check prodset evens empte -- empty
#check prodset evens ods


/- subset

Given two sets, s1 and s2, of objects of some type 
T, we say that s1 is a subset of s2, written s1 ⊆ s2,
if every element in s1 is in s2. We say that s1 is a
proper subset of s2, written s1 ⊂ s2, if every value
in s1 is in s2 and some value in s2 is not in s1. 
-/

#check evens ⊆ evens -- true
#check evens ⊂ evens -- false
#check evens ⊆ complete -- true
#check evens ⊂ complete -- true
#check evens ⊂ empte -- false
#check ∀ (s : set ℕ), empte ⊆ s -- unsure


/- powerset

The powerset of a set, s, written 𝒫 s, is 
the set of all subsets of s. This makes the 
powerset a set of sets. 
-/

#check 𝒫 { 1, 2, 3}
#check 𝒫 evens


/-
Now let's state and prove some theorems.
-/


example : ∀ (n : ℕ), evens_union_ods n ↔ complete n := 
_


example : ∀ (n : ℕ), (n ∈ evens_union_ods) ↔ (n ∈ complete) := 
_


/-
Now we are in a position to see formal 
definitions of all of the preceding set
theory concepts.
-/

axioms (P Q : ℕ → Prop)

def pSet  : set nat := { n : ℕ | P n}
def qSet  : set nat := { n : ℕ | Q n}

#reduce 0 ∈ pSet
#reduce pSet ∪ qSet
#reduce pSet ∩ qSet
#reduce pSet \ qSet
#reduce pSet ⊆ qSet
#reduce 𝒫 pSet      -- harder to decipher


/-
Now that we understand these operations and
their corresponding notations in set theory,
we can start to state and prove theorems!
-/


