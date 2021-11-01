import data.set

/-
Exercise: Prove that for any set, L, L ∩ L = L.

L intersects with L is equal to L because the
intersect operator identifies values which
exist within both subsets, meaning it takes
values from s1 and s2. We are comparing
the exact same set, L, so the resulting set would
contain all the values found in both sets. Both
sets are equal, so the result would be an exact
copy of both sets.   
-/


/-
Exercise: Give a formal statement and proof, then an 
English language proof, that the union operator on 
sets is commutative.

-- answer:
The union operator is commutative because the same 
subset can be identified regardless of the order of
the original two because of the fact that the union
operator identifies a subset of the values
from the first or the second set. Therefore, order
of sets is irrelevant because the subset would not
include any different values as a result of changing
order.     

The union operator is commutative because the resulting set
does not depend on the order of the original sets. This means
that the resulting set would contain the same values regardless
of the order of sets being compared. This is because the union
operator indentifies a set which is in the first set OR the
second set, so regardless of order both sets are properly
included. 
-/


/-
Exercise: Prove that ⊆ is reflexive and transitive.
Give a formal statement, a formal proof, and an English
language (informal) proof of this fact.

Statement : The subset of two sets is reflexive and transitive 

formal proof : The subset of a set is reflexive because the
resulting sets are equal to eachother, and by the reflexive
property a value is always equal to itself.
                The subset of a set is transitive because the 
resulting sets are equal to eachother, so by the transitive
property you can deduce that identifiying a subset also
implies these sets to be equal. 

informal proof : A subset of a set is one which contains every
value already present in the first set.  In this case, the line
under the symbol means every value in the first set is also in
the second set. Therefore it satisfies the reflexive property 
because the sets being compared are equal. It is transitive
because the sets are completely equal and therefore can be treated
the same way as single variables which equal eachother.  
-/


/-
Exercise: Prove that ∪ and ∩ are associative.
Give a formal statement, a formal proof, and an 
English language (informal) proof of this fact.

Statement : The union of two sets and the intersection of two sets are both
associative properties

English language: The union and intersection of sets is
associative because the values will not change based on
the direction they are being compared. 
-/


/-
Assignment: read (at least skim) the Sections 1 and 
2 of the Wikipedia page on set identities: 
https://en.wikipedia.org/wiki/List_of_set_identities_and_relations 
There, , among *many* other facts, you will find definitions 
of left and right distributivity. To complete the remainder
of this assignment, you need to understand what it means for 
one operator to be left- (or right-) distributive over another. 
-/


/-
Exercise: Formally state, and prove both formally and 
informally, that ∩ is left-distributive over ∩.
-/


/-
Exercise: Formally state and prove both formally 
and informally that ∪ is left-distributive over ∩.
-/


