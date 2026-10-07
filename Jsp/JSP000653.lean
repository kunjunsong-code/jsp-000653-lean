import Init.Data.List.Basic
import Init.Data.List.Lemmas

set_option maxRecDepth 1000000

/-!
# JSP-000653 - Lean 4.20.0, no Mathlib

## Question
How large can a subset of an integer interval be if all subset
products are distinct?

## Answer (for {2,...,10})
Maximum size = 6. An explicit example is {2, 3, 4, 5, 7, 9}.

Proof:
1. We exhibit an explicit 6-element subset of {2,...,10} where all
   2^6 - 1 = 63 nonempty subset products are distinct.
2. We verify by exhaustive check of all C(9,7) = 36 subsets of
   size 7 that every 7-element subset of {2,...,10} contains two
   distinct nonempty subsets with the same product.

All proofs use decide. No sorry, no admit, no native_decide.
-/

def powerSet {alpha : Type} : List alpha -> List (List alpha)
  | []      => [[]]
  | (x::xs) => (powerSet xs).map (fun s => x :: s) ++ powerSet xs

def listProd : List Nat -> Nat
  | []      => 1
  | (x::xs) => x * listProd xs

def nonemptySubsetProducts (S : List Nat) : List Nat :=
  (powerSet S).filter (fun s => ! s.isEmpty) |>.map listProd

def hasDuplicate : List Nat -> Bool
  | []      => false
  | (x::xs) => xs.contains x || hasDuplicate xs

def allProductsDistinct (S : List Nat) : Bool :=
  ! hasDuplicate (nonemptySubsetProducts S)

/-!
## Part 1: Construction -- explicit 6-element subset with distinct subset products
-/

def S6 : List Nat := [2, 3, 4, 5, 7, 9]

theorem S6_length : S6.length = 6 := by decide

theorem S6_in_range : (S6.all (fun x => 2 <= x && x <= 10)) = true := by decide

theorem S6_allProductsDistinct : allProductsDistinct S6 = true := by decide

/-!
## Part 2: All C(9,7) = 36 seven-element subsets have a product collision
-/

def all7Subsets : List (List Nat) :=
  [[4,5,6,7,8,9,10],[3,5,6,7,8,9,10],[3,4,6,7,8,9,10],[3,4,5,7,8,9,10],
   [3,4,5,6,8,9,10],[3,4,5,6,7,9,10],[3,4,5,6,7,8,10],[3,4,5,6,7,8,9],
   [2,5,6,7,8,9,10],[2,4,6,7,8,9,10],[2,4,5,7,8,9,10],[2,4,5,6,8,9,10],
   [2,4,5,6,7,9,10],[2,4,5,6,7,8,10],[2,4,5,6,7,8,9],
   [2,3,6,7,8,9,10],[2,3,5,7,8,9,10],[2,3,5,6,8,9,10],[2,3,5,6,7,9,10],
   [2,3,5,6,7,8,10],[2,3,5,6,7,8,9],
   [2,3,4,7,8,9,10],[2,3,4,6,8,9,10],[2,3,4,6,7,9,10],[2,3,4,6,7,8,10],
   [2,3,4,6,7,8,9],
   [2,3,4,5,8,9,10],[2,3,4,5,7,9,10],[2,3,4,5,7,8,10],[2,3,4,5,7,8,9],
   [2,3,4,5,6,9,10],[2,3,4,5,6,8,10],[2,3,4,5,6,8,9],
   [2,3,4,5,6,7,10],[2,3,4,5,6,7,9],
   [2,3,4,5,6,7,8]]

theorem no_7_element_subset :
    all7Subsets.all (fun S => ! allProductsDistinct S) = true := by decide

/-!
## Main theorem
-/

theorem jsp_000653_main :
    S6.length = 6 /\
    allProductsDistinct S6 /\
    (S6.all (fun x => 2 <= x && x <= 10)) /\
    all7Subsets.all (fun S => ! allProductsDistinct S) = true :=
  by decide

#print axioms jsp_000653_main
