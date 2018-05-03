# Evaluation

Tests that we have created are structured in 4 folders:
 * Advanced : Complex tests that are testing more than one error, contain domains, axioms etc ...
 * Algorithms : Implementations of some well known algorithms that could be implemented in our limited setup.
 * Laws: Axioms in boolean and integer arithmetics that have to always hold.
 * Unit : Unit tests that focus on one particular error type, no domains ...
 
 ## Advanced
 **We have created following advanced tests:**
  * Graph paths
  * Complete graph paths
  * Reverse of a sequence
 
 ## Algorithms
 **We have implemented following algorithms:**
  * Binary search for a number
  * Binary search on a sorted sequence
  * Vector addition
  * Inner product of two vectors ????
 
 ## Laws
 **Boolean algebra:**
  * Commutativity law
  * Associativity law
  * Distributivity law
  * Identity law
  * Annihilator 
  * Indempotence
  * Absorbtion
  
 **Integer arithmetics:**
  * Selected laws that should hold in integer arithmetics
  
 ## Unit
 **Error types that we test for:**
  * Assertion might fail
  * Invariant might not be preserved
  * Invariant does not 
  * Postcondition might not hold
 
# Bonus: Matrix addition

To fix the failing assert inside the inner loop we introduced the following loop invariants dealing
with the range of loop indexes (i.e., i and j) and ensuring that the matrices have the same size.

**Outer Loop Invariants**

    invariant i >= 0 && i <= size(m1)
    invariant size(m1) == size(m2) && size(m1) == size(m3)


**Inner Loop Invariants**

    invariant j >= 0 && j <= size(m2)
    invariant size(m1) == size(m2) && size(m1) == size(m3)

However, these invariants hold only if we add the following trivial method precondition.

    requires size(m1) >= 0

To make the method's postcondition verify we had to introduce the following additional loop invariants.

**Outer Loop Invariants**

    invariant forall x: Int, y: Int :: {select(m3,x,y)}
      inRange(m3, x, y) && x < i ==> select(m3,x,y) == select(m1,x,y) + select(m2,x,y)

Guarantees that for every x and y in valid range where x is less than the current i (row index),
`m3[x,y] = m1[x,y] + m2[x,y]`.

**Inner Loop Invariants**

    invariant forall x: Int, y: Int :: {select(m3,x,y)}
      inRange(m3, x, y) && x < i ==> select(m3,x,y) == select(m1,x,y) + select(m2,x,y)

Guarantees that for every x and y in valid range where x is less than the current i (row index),
`m3[x,y] = m1[x,y] + m2[x,y]`.

    invariant forall x: Int, y: Int :: {select(m3,x,y)}
      inRange(m3, x, y) && x == i && y < j ==> select(m3,x,y) == select(m1,x,y) + select(m2,x,y)

Guarantees that for every x and y in valid range where x is equal to the current i (row index)
and y is less than the current j (column index), `m3[x,y] = m1[x,y] + m2[x,y]`.

All in all, these invariants guarantee that during the looping process of all the matrix cells,
already visited cells retain appropriate values.