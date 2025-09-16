-- https://leanprover.github.io/theorem_proving_in_lean4/inductive_types.html#other-recursive-data-types

namespace Hidden

inductive List (α : Type u) where
| nil  : List α
| cons : α → List α → List α

namespace List

def append (as bs : List α) : List α :=
 match as with
 | nil       => bs
 | cons a as => cons a (append as bs)

theorem nil_append (as : List α) : append nil as = as :=
 rfl

theorem cons_append (a : α) (as bs : List α)
                    : append (cons a as) bs = cons a (append as bs) :=
 rfl

theorem append_nil (as : List α) : append as nil = as :=
  sorry

-- solution:
theorem append_nil1 (as : List α) : append as nil = as :=
  match as with
  | nil => rfl
  | cons a as' => by rw [append, append_nil as']


theorem append_nil2 (as : List α) : append as nil = as :=
  List.recOn as
    (by rfl)  -- Base case: append nil nil = nil
    (fun a as' ih => by rw [append, ih])  -- Inductive case


theorem append_assoc (as bs cs : List α)
        : append (append as bs) cs = append as (append bs cs) :=
  sorry
end List
end Hidden




-- //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
-- https://leanprover.github.io/theorem_proving_in_lean4/inductive_types.html#tactics-for-inductive-types

namespace Hidden
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.add_succ, ih]
end Hidden

theorem zero_add2 (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => -- ⊢ 0 + (n + 1) = n + 1
    calc
      0 + (n + 1)
      -- ∀ (n m : Nat), n + m.succ  = (n + m).succ
      --                0 + (n + 1) = (0 + n).succ := by rw [Nat.add_succ]
      _ = succ (0 + n) := by rw [Nat.add_succ]
      _ = succ (n)  := by rw [ih] -- 0 + n = n by ih, and: succ (n) = n + 1

theorem zero_add3 (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      0 + n.succ = (0 + n).succ := by rw [Nat.add_succ]
      _          = n.succ       := by rw [ih]




-- Here are some additional examples:
namespace Hidden
theorem add_zero (n : Nat) : n + 0 = n := Nat.add_zero n
open Nat

theorem zero_add (n : Nat) : 0 + n = n := by
  induction n <;> simp [*, add_zero, add_succ]

/-
tactic 'simp' failed, nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
-- theorem succ_add (m n : Nat) : succ m + n = succ (m + n) := by
--  induction n <;> simp [*, add_zero, add_succ]

theorem succ_add2 (m n : Nat) : succ m + n = succ (m + n) := by
  induction n with
  | zero => rw [add_zero]   -- | zero => rfl
  | succ n =>
     calc
        m.succ + (n + 1)
        _ = n.succ + m.succ := by rw [Nat.add_comm]
        _ = (n.succ + m).succ := by rw [Nat.add_succ]
        _ = (m + n.succ).succ := by rw [Nat.add_comm]



theorem add_comm (m n : Nat) : m + n = n + m := by
  induction n <;> simp [*, add_zero, add_succ, succ_add, zero_add]

theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) := by
  induction k <;> simp [*, add_zero, add_succ]
end Hidden




-- //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
-- https://leanprover.github.io/theorem_proving_in_lean4/inductive_types.html#inductive-families

/-
The Vector type is a length-indexed list — a list that carries its length in its type. This lets Lean track and enforce length information at compile time, which is very powerful for ensuring correctness.
-/

-- Here’s a breakdown of the definition:
namespace Hidden
inductive Vector (α : Type u) : Nat → Type u where
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)

/-
The Vector definition means:
    - A Vector α n is a list of elements of type α of exact length n.
    - nil represents the empty vector.
    - cons adds one element in front and increases the length by 1.
-/

-- Examples
open Vector

-- A Vector Nat 0 (an empty vector of Nat)
def v0 : Vector Nat 0 := nil

-- A Vector String 0 (an empty vector of String)
def v0S : Vector String 0 := nil

-- A Vector Nat 1 (with one element)
def v1 : Vector Nat 1 := cons 5 nil

-- A Vector Nat 2
def v2 : Vector Nat 2 := cons 3 (cons 4 nil)

-- A Vector String 3
def v3 : Vector String 3 := cons "a" (cons "b" (cons "c" nil))


-- Because the length is encoded in the type, certain bugs are impossible:
-- This will cause a compile-time error because the lengths don't match:
def bad : Vector Nat 2 := cons 1 nil
-- Lean will tell you the types don't match because cons 1 nil has type Vector Nat 1, not Vector Nat 2.


def map {α β : Type u} {n : Nat} (f : α → β) : Vector α n → Vector β n
  | nil        => nil
  | cons a as  => cons (f a) (map f as)

#eval map (fun x => x + 1) (cons 1 (cons 2 nil)) -- Vector Nat 2 with values [2, 3]

end Hidden

/-
Why does cons need a number like cons 5, but nil doesn't?
This is all about how the constructor types of Vector work in Lean.

The definition of Vector:
    inductive Vector (α : Type u) : Nat → Type u where
      | nil  : Vector α 0
      | cons : α → {n : Nat} → Vector α n → Vector α (n+1)


Let’s look at each constructor:
    nil : Vector α 0

nil doesn’t take any arguments.
It simply gives you a vector of length 0.
So to build a Vector Nat 0, you just write:
    def v0 : Vector Nat 0 := nil

Easy! No numbers or elements are needed, because a vector of length 0 has no elements.


    cons : α → {n : Nat} → Vector α n → Vector α (n+1)

cons adds an element to the front of a vector.
It takes two arguments:
An element of type α (e.g. a number like 5)
A smaller vector (with length n)
It returns a new vector with length n + 1.
So cons needs a value to add, like 5, and the rest of the vector to attach it to.

Example:
    def v1 : Vector Nat 1 := cons 5 nil


Here’s what happens:

5 is the value of type Nat
nil is Vector Nat 0
So cons 5 nil is Vector Nat 1


Summary
Constructor	Needs an element?	Needs a previous vector?	Resulting length
nil         No	                No	                        0
cons	    Yes	                Yes	                        n + 1
-/
