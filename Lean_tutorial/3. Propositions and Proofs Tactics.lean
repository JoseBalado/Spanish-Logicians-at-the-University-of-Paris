-- ## Notes
-- Use preferably the following.
-- 1. And.intro for ∧ introduction.

-- 2. And.left and And.right for ∧ elimination.
-- or even better, use 'have' to simulate another step in the proof.
/-
p ∧ q → p

1 |_ p ∧ q
2 | p        And.left 1
3 p ∧ q → q  Conditional proof
-/
example : p ∧ q → p := by
  intro (h : p ∧ q)
  have hp : p := And.left h -- corresponds to line 2, making the structure of the proof more clear.
  exact hp
-- or compressing the last two steps:
example : p ∧ q → p := by
  intro (h : p ∧ q)
  exact (And.left h : p)

-- 3. Or.inl and Or.inr for ∨ introduction.

-- 4. 'cases-with' for ∨ elimination.
example : p ∨ q → q ∨ p := by
  intro (h : p ∨ q)
  cases h with
  | inl hp => exact (Or.inr hp : (q ∨ p))
  | inr hq => exact (Or.inl hq : (q ∨ p))

-- 5. Use Definition of ¬ for more clarity in the natural deduction diagrams.
-- Also, to have an 'intro' inside a 'have', 'by' is needed, as shown in this example.
/-
¬(p ∨ q) ↔ ¬p ∧ ¬q

1  |_ ¬(p ∨ q)
2  |  |_ p
3  |  |  p ∨ q                Or.inl 2
4  |  |  False                Apply 1,3
5  |  p → False               Conditional proof 2-4
6  |  ¬ p                     ¬ Definition 5

7  |  |_ q
8  |  |  p ∨ q                Or.inr 7
9  |  |  False                Apply 1,8
10 |  q → False               Conditional proof 7-9
11 |  ¬ q                     ¬ Definition 10
12 |  ¬p ∧ ¬q                 And.intro 6,11
13 ¬(p ∨ q) → ¬p ∧ ¬q         Conditional proof 1-12
-/
example : ¬(p ∨ q) →  ¬p ∧ ¬q := by
  intro (hnpq : ¬(p ∨ q))
  have hpFalse : p → False := by        -- 'by' is needed to have an 'intro' inside a 'have'
    intro (hp : p)
    have hpq : p ∨ q := Or.inl hp
    exact (hnpq hpq : False)
  have hnp : ¬p := hpFalse             -- This step is not needed as 'p → False' is equivalent to '¬p'.
  have hnq : ¬q := by
    intro (hq : q)
    have hpq : p ∨ q := Or.inr hq
    exact (hnpq hpq : False)
  exact And.intro hnp hnq

-- 6. byContradiction is equivalent to Double Negation Elimination (DNE) or to Excluded Middle (EM).
-- Inside 'have' and also after 'exact' we are again in term mode.
example (h : ¬¬p) : p := by
  exact Classical.byContradiction h

example (h : ¬¬p) : p := by
  have hp : p :=                 -- Inside 'have' we are in term mode.
    Classical.byContradiction h
  exact hp

example : ¬¬p → p := by
  intro (hnnp : ¬¬p)
  exact Classical.byContradiction (by exact hnnp)  -- 'by' allows to use tactics inside 'byContradiction'.

example : ¬(p → q) → p := by
  intro (hnpq : ¬(p → q))
  exact Classical.byContradiction (by  -- 'by' allows to use tactics inside 'byContradiction'.
      intro hnp
      have hpq : p → q := by
        intro (hp : p)
        have hFalse : False := hnp hp
        exact (False.elim hFalse : q)
      exact (hnpq hpq : False))


/-
In Lean, both cases and match can be used to perform case analysis (pattern matching) on inductive types like Or, And, or Nat. However, their usage and context differ:

cases (tactic mode):

Used in tactic proofs (inside by blocks).
Splits a hypothesis or goal into cases, creating new subgoals for each constructor.
Syntax:
```
cases h with
| inl hp => ...
| inr hq => ...
```

It is procedural and works step-by-step, modifying the proof state.
match (term mode or tactic mode):

Used in term proofs (functional style) and also inside tactic mode.
Allows you to write pattern matching expressions directly, returning a value based on the cases.
Syntax:
```
match h with
| Or.inl hp => ...
| Or.inr hq => ...
```
It is more like a functional programming construct, returning a value.
-/

-- https://leanprover.github.io/theorem_proving_in_lean4/propositions_and_proofs.html#working-with-propositions-as-types

variable {p q : Prop}

/-
p → q → p

1  |_ p
2  |  |_ q
3  |  |  p    Reiteration
4  |  q → p   Conditional proof 2-3
5  p → q → p  Conditional proof 1-4
-/
example : p → q → p := by
  intro (hp : p)
  intro (hq : q)
  exact hp

example : p → q → p := by
  intros hp hq
  exact hp

example : p → q → p := by
  intro hp
  intro _
  exact hp


example : p → q → p := by
  intro hp
  intro
  exact hp

example : p → q → p := by
  intro hp
  intro
  repeat assumption

-------------------------------------------------------------------------------------------
/-
p ⊢ p or equivalently p : p

1  p
3  p  Reiteration
-/
theorem t1 (hp : p) : p := by
  exact hp


-----------------------------------------------------------------------------------------------
/-
q ⊢ p → q

1  q
2  |_ p
3  |  q    Reiteration
4  q → p   Conditional proof 2-3
-/
example (hp : p) : q → p := by
  intro (hq : q)
  exact hp

example (hp : p) : q → p := by
  intro
  exact hp

example (hp : p) : q → p := by
  intro _
  exact hp

example (hp : p) : q → p := by
  intro (hq : q)
  repeat assumption


--------------------------------------------------------------------------------------------------
-- Tactics Examples not in the book
/-
'False' is equivalent to '⊥'.
False.elim is equivalent to 'Ex Falso Quodlibet'.

¬p → p → q

1  |_ ¬p
2  |  |_ p
3  |  |  False    Apply 1,2
3  |  |  q        False.elim 3 (From 'False' we can derive anything, 'q' in this case)
4  |  p → q       Conditional proof 2-3
5  ¬p → p → q     Conditional proof 1-4
-/
example : ¬p → p → q := by
  intro (hnp : ¬p)
  intro (hp : p)
  exact (False.elim (hnp hp : False) : q)

example : ¬p → p → q := by
  intros hnp hp
  exact False.elim (hnp hp)

example : ¬p → p → q := by
  intro hnp
  intro hp
  exact absurd hp hnp

example : ¬p → p → q := by
  intro hnp
  intro hp
  contradiction

----------------------------------------------------------------------------------------------------------
-- Examples not in the book

/-
byContradiction is equivalent to Double Negation Elimination (DNE) or to Excluded Middle (EM).

¬¬p : p
-/
example (h : ¬¬p) : p := by
  have hp : p := Classical.byContradiction h
  exact hp

/-
¬¬p → p

1  |_ ¬¬p
2  |  p     byContradiction 1
3  ¬¬p → p  Conditional proof 1-2
-/
example : ¬¬p → p := by
  intro hnnp
  have hp : p := Classical.byContradiction hnnp
  exact hp


/-
¬p, p ⊢ q

1  ¬p
2  p
3  False    Apply 1,2
4  q        False.elim 3
-/
example (hnp : ¬p) (hp : p) : q := by
  exact (False.elim (hnp hp) : q)

example (hnp : ¬p) (hp : p) : q := by
  exact absurd hp hnp

example (hnp : ¬p) (hp : p) : q := by
  contradiction

----------------------------------------------------------------------------------------------------------
/-
1  ¬p
2  |_ p
3  |  False   Apply 1,2
4  |  q       False.elim
5  p → q
-/
example (hnp : ¬p) : p → q := by
  intro (hp : p)
  exact (False.elim (hnp hp) : q)

example (hnp : ¬p) :  p → q := by
  intro (hp : p)
  exact absurd hp hnp

example (hnp : ¬p) :  p → q := by
  intro (hp : p)
  contradiction


----------------------------------------------------------------------------------------------------------------
-- As a chain of implications.
/-
¬p → p → q

1 |_ ¬p
2 |  |_ p
3 |  |  False    Apply 1,2
4 |  |  q        False.elim 3
5 |  p → q       Conditional proof 2-4
6 ¬p → p → q     Conditional proof 1-5
-/
example : ¬p → p → q := by
  intro (hnp : ¬p)
  intro (hp : p)
  exact (False.elim (hnp hp) : q)

example : ¬p → p → q := by
  intro (hnp : ¬p)
  intro (hp : p)
  exact (absurd hp hnp : q)

example : ¬p → p → q := by
  intro (hnp : ¬p)
  intro (hp : p)
  contradiction

/-
(p → q) ∨ (q → p)

1  p ∨ ¬p                  Excluded Middle (em p)
2  |_ p
3  |  |_ q
4  |  |  p                 Reiteration
3  |  q → p                Conditional proof 3-4
4  |  (p → q) ∨ (q → p)    Or.inr 3

5  |_ ¬p
6  |  |_ p
7  |  |  False              Apply 5,6
8  |  |  q                  False.elim 7
9  |  p → q                 Conditional proof 6-8
10 |  (p → q) ∨ (q → p)     Or.inr 9

11 (p → q) ∨ (q → p)        Or.elim 1, 2-4, 5-10
-/
-- Using dot '.' as an indentation helper.
-- using cases to eliminate Tertio Excluso.
example : (p → q) ∨ (q → p) := by
  cases Classical.em p with
  | inl hp =>
    have hpq : q → p := by   -- 'by' is required here to open a new proof block, allowing the use of 'intro' within 'have'.
      intro (hq : q)
      exact hp
    exact (Or.inr hpq : (p → q) ∨ (q → p))
  | inr hnp =>
    have hpq : p → q := by
      intro (hp : p)
      have false : False := hnp hp
      exact (False.elim false : q)
    exact (Or.inl hpq : (p → q) ∨ (q → p))

-- Using apply and Or.elim to eliminate tertio excluso.
example : (p → q) ∨ (q → p) := by
  apply Or.elim (Classical.em p)
  . intro (hp : p)
    . apply Or.inr
      intro (hq : q)
      exact hp
  . intro (hnp : ¬p)
    . apply Or.inl
      intro (hp : p)
      exact (False.elim (hnp hp) : q)

-- Mix between tactics and term proofs
example : (p → q) ∨ (q → p) := by
  apply Or.elim (Classical.em p)
    (fun hp : p => Or.inr (fun _ => hp))
    (fun hnp : ¬p => Or.inl (fun hp => False.elim (hnp hp)))

-- #########################################################################################
-- 3.6. Examples of Propositional Validities
-- #########################################################################################
-- All are included in 3.7 Exercises.


-- #########################################################################################
-- 3.7 Exercises
-- #########################################################################################
variable (p q r : Prop)

-- ## commutativity of ∧ and ∨
/-
p ∧ q ↔ q ∧ p

1  |_ p ∧ q
2  |  p              And.left
3  |  q              And.right
4  |  q ∧ p          And.intro 3,2
5  p ∧ q → q ∧ p     Conditional proof 1-4

6  |_ q ∧ p
7  |  q              And.left
8  |  p              And.right
9  |  p ∧ q          And.intro 8,7
10 q ∧ p → p ∧ q     Conditional proof 6-9

11 p ∧ q ↔ q ∧ p     Iff.intro 5,10
-/
example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro
  · intro (hpq : p ∧ q)
    . have hp := And.left hpq
      have hq := And.right hpq
      exact (And.intro hq hp : q ∧ p)
  · intro (hpq : q ∧ p)
    . have hq := And.right hpq
      have hp := And.left hpq
      exact (And.intro hq hp : p ∧ q)

-- Using 'apply' only to 'Iff.intro' and term mode for the rest.
example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro
    (fun h => And.intro h.right h.left)
    (fun h => And.intro h.right h.left)

-- Using 'have' plus term mode to apply Iff.intro at the end.
-- Example of using 'this' notation.
example : p ∧ q ↔ q ∧ p := by
  have hqp : p ∧ q → q ∧ p := fun hpq =>
    have hp := And.left hpq
    have := And.right hpq
    And.intro this hp
  have hpq : q ∧ p → p ∧ q := fun hqp =>
    have := And.left hqp
    have hp := And.right hqp
    And.intro hp this
  exact Iff.intro hqp hpq

example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro
  · intro (h : p ∧ q)
    exact (And.intro (And.right h) (And.left h) : q ∧ p)
  · intro (h : q ∧ p)
    exact (And.intro (And.right h) (And.left h) : p ∧ q)

example : p ∧ q ↔ q ∧ p := by
  constructor
  · intro h
    apply And.intro
    . case left => exact h.right
    . case right => exact h.left
  · intro h
    apply And.intro
    . case left => exact h.right
    . case right => exact h.left

example : p ∧ q ↔ q ∧ p := by
  constructor
  · intro h
    apply And.intro
    . exact And.right h
    . exact And.left h
  · intro h
    apply And.intro
    . exact And.right h
    . exact And.left h

-- Using 'cases' instead of 'apply And.intro'.
example : p ∧ q ↔ q ∧ p := by
  constructor
  · intro h
    cases h with
    | intro hp hq =>
      exact ⟨hq, hp⟩
  · intro h
    cases h with
    | intro hq hp =>
      exact ⟨hp, hq⟩

-- Using 'match' instead of 'apply And.intro'.
example : p ∧ q ↔ q ∧ p := by
  constructor
  · intro h
    exact match h with
    | ⟨hp, hq⟩ => ⟨hq, hp⟩
  · intro h
    exact match h with
    | ⟨hq, hp⟩ => ⟨hp, hq⟩

-- Using '⟨ ⟩' directly.
example : p ∧ q ↔ q ∧ p := by
  constructor
  · intro h
    exact ⟨h.right, h.left⟩
  · intro h
    exact ⟨h.right, h.left⟩


-----------------------------------------------------------------------------------------------
/-
p ∨ q ↔ q ∨ p

1  |_ p ∨ q
2  |  |_ p
3  |  |  q ∨ p          Or.inr 2

4  |  |_ q
5  |  |  q ∨ p          Or.inl 4
6  |  q ∨ p             Or.elim 1, 2-3, 4-5
7  p ∨ q → q ∨ p        Conditional proof 2-6

8  |_ q ∨ p
9  |  |_ q
10 |  |  p ∨ q          Or.inr 9

11 |  |_ p
12 |  |  p ∨ q          Or.inl 11
13 |  p ∨ q             Or.elim 8, 9-10, 11-12
14 q ∨ p → p ∨ q        Conditional proof 8-13

15 p ∨ q ↔ q ∨ p        Iff.intro 7,14
-/
example : p ∨ q ↔ q ∨ p := by
  constructor
  . intro (h : p ∨ q)
    cases h with
    | inl hp => exact (Or.inr hp : q ∨ p)
    | inr hq => exact (Or.inl hq : q ∨ p)
  . intro (h : q ∨ p)
    cases h with
    | inl hq => exact (Or.inr hq : p ∨ q)
    | inr hp => exact (Or.inl hp : p ∨ q)

example : p ∨ q ↔ q ∨ p := by
  constructor
  . intro (h : p ∨ q)
    cases h with
    | inl hp =>
      have hqp : q ∨ p := Or.inr hp
      exact hqp
    | inr hq =>
      have hqp : q ∨ p := Or.inl hq
      exact hqp
  . intro (h : q ∨ p)
    cases h with
    | inl hq =>
      have hqp : p ∨ q := Or.inr hq
      exact hqp
    | inr hp =>
      have hqp : p ∨ q := Or.inl hp
      exact hqp

-- (unstructured) cases without the 'with' and a tactic for each alternative:
example : p ∨ q ↔ q ∨ p := by
  apply Iff.intro
  . intro (h : p ∨ q)
    cases h
    . case inl hp => apply Or.inr hp
    . case inr hq => apply Or.inl hq
  . intro (h : q ∨ p)
    cases h
    . case inl hq => exact Or.inr hq
    . case inr hp => exact Or.inl hp


-- #################################################################################################
-- ## associativity of ∧ and ∨
/-
(p ∧ q) ∧ r ↔ p ∧ (q ∧ r)

1  |_ (p ∧ q) ∧ r
2  |  p ∧ q                       And.left 1
3  |  p                           And.left 2
4  |  q                           And.right 2
5  |  r                           And.right 1
6  |  q ∧ r                       And.intro 4,5
7  |  p ∧ (q ∧ r)                 And.intro 3,6
8  (p ∧ q) ∧ r → p ∧ (q ∧ r)      Conditional proof 1-6

9  |_ p ∧ (q ∧ r)
10 |  p                           And.left 8
11 |  q                           And.left (And.right 8)
12 |  r                           And.right (And.right 8)
13 |  p ∧ q                       And.intro 10, 11
14 |  (p ∧ q) ∧ r                 And.intro 13, 12
15 p ∧ (q ∧ r) → (p ∧ q) ∧ r      Conditional proof 9-14

16 (p ∧ q) ∧ r ↔ p ∧ (q ∧ r)      Iff.intro 8, 15
-/
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  apply Iff.intro
  . intro (h : (p ∧ q) ∧ r)
    have hpq : p ∧ q := And.left h
    have hp : p := And.left hpq
    have hq : q := And.right hpq
    have hr : r := And.right h
    have hqr : q ∧ r := And.intro hq hr
    exact (And.intro hp hqr : p ∧ (q ∧ r))
  . intro (h : p ∧ (q ∧ r))
    have hp : p := And.left h
    have hq : q := And.left (And.right h)
    have hr : r := And.right (And.right h)
    have hpq : p ∧ q := And.intro hp hq
    exact (And.intro hpq hr : (p ∧ q) ∧ r)

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  constructor
  . intro (h : (p ∧ q) ∧ r)
    exact And.intro h.left.left (And.intro h.left.right h.right)
  . intro (h : p ∧ (q ∧ r))
    exact And.intro (And.intro h.left h.right.left) h.right.right


---------------------------------------------------------------------------------------------------------------------
/-
(p ∨ q) ∨ r ↔ p ∨ (q ∨ r)

1  |_ (p ∨ q) ∨ r
2  |  |_ p ∨ q
3  |  |  |_ p
4  |  |  |  p ∨ (q ∨ r)         Or.inl 3

5  |  |  |_ q
6  |  |  |  q ∨ r               Or.inl 5
7  |  |  |  p ∨ (q ∨ r)         Or.inr 6
8  |  |  p ∨ (q ∨ r)            Or.elim 2, 3-4, 5-7

9  |  |_ r
10 |  |  q ∨ r                  Or.inr 9
11 |  |  p ∨ (q ∨ r)            Or.inr 10
12 |  (p ∨ q) ∨ r               Or.elim 1, 2-8, 9-11
13 (p ∨ q) ∨ r → p ∨ (q ∨ r)    Conditional proof 1-12

14 |_ p ∨ (q ∨ r)
15 |  |_ p
16 |  |  p ∨ q                  Or.inl 15
17 |  |  (p ∨ q) ∨ r            Or.inl 16

18 |  |_ q ∨ r
19 |  |  |_ q
20 |  |  |  p ∨ q               Or.inl 19
21 |  |  |  (p ∨ q) ∨ r         Or.inl 20

22 |  |  |_ r
23 |  |  |  (p ∨ q) ∨ r         Or.inr 22
24 |  |  (p ∨ q) ∨ r            Or.elim 18, 19-21, 22-23
25 |  (p ∨ q) ∨ r               Or.elim 14, 15-15, 18-24
26 p ∨ (p ∨ q) → (p ∨ q) ∨ r    Conditional proof 14-25

27 (p ∨ q) ∨ r ↔ p ∨ (q ∨ r)    Iff.intro 13,26
-/
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  apply Iff.intro
  . intro (hpqr : (p ∨ q) ∨ r)
    cases hpqr with
    | inl hpq =>
      cases hpq with
      | inl hp =>
        exact (Or.inl hp : p ∨ (q ∨ r))
      | inr hq =>
        have hqr : q ∨ r := Or.inl hq
        exact (Or.inr hqr : p ∨ (q ∨ r))
    | inr hr =>
      have hqr : q ∨ r := Or.inr hr
      exact (Or.inr hqr : p ∨ (q ∨ r))
  . intro (hpqr : p ∨ (q ∨ r))
    cases hpqr with
    | inl hp =>
      have hpq : p ∨ q := Or.inl hp
      exact (Or.inl hpq : (p ∨ q) ∨ r)
    | inr hqr =>
      cases hqr with
      | inl hq =>
        have hpq : p ∨ q := Or.inr hq
        exact (Or.inl hpq : (p ∨ q) ∨ r)
      | inr hr =>
        exact (Or.inr hr : (p ∨ q) ∨ r)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  apply Iff.intro
  . intro (hpqr : (p ∨ q) ∨ r)
    apply Or.elim hpqr
    . intro (hpq : p ∨ q)
      apply Or.elim hpq
      . intro (hp : p)
        exact Or.inl hp
      . intro (hq : q)
        exact Or.inr (Or.inl hq)
    . intro (hr : r)
      exact Or.inr (Or.inr hr)
  . intro (hpqr : p ∨ (q ∨ r))
    apply Or.elim hpqr
    . intro (hp : p)
      exact Or.inl (Or.inl hp)
    . intro (hqr : q ∨ r)
      apply Or.elim hqr
      . intro (hq : q)
        exact Or.inl (Or.inr hq)
      . intro (hr : r)
        exact Or.inr hr

-- ###########################################################################################################
-- ## distributivity
/-
p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)

1  |_ p ∧ (q ∨ r)
2  |  p                                  And.left 1
3  |  q ∨ r                              And.right 1
4  |  |_ q
5  |  |  p ∧ q                           And.intro 2,4
6  |  |  (p ∧ q) ∨ (p ∧ r)               Or.inl 5

7  |  |_ r
8  |  |  p ∧ r                           And.intro 2,7
9  |  |  (p ∧ q) ∨ (p ∧ r)               Or.inr 8
10 |  (p ∧ q) ∨ (p ∧ r)                  Or.elim 3, 4-6, 7-9
11 p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r)       Conditional proof 1-10

12 |_ (p ∧ q) ∨ (p ∧ r)
13 |  |_ p ∧ q
14 |  |  p                              And.left 14
15 |  |  q                              And.right 15
16 |  |  q ∨ r                          Or.inl 15
17 |  |  p ∧ (q ∨ r)                    And.intro 14,16

18 |  |_ p ∧ r
19 |  |  p                              And.left 18
20 |  |  r                              And.right 18
21 |  |  q ∨ r                          Or.inr 20
22 |  |  p ∧ (q ∨ r)                    And.intro 19,21
23 |  p ∧ (q ∨ r)                       Or.elim 12, 13-17, 18-22
24 (p ∧ q) ∨ (p ∧ r) → p ∧ (q ∨ r)      Conditional proof 18-23

25 p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)      Iff.intro 11,24
-/
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro (hpqr : p ∧ (q ∨ r))
    have hp : p := And.left hpqr
    have hqr : q ∨ r := And.right hpqr
    cases hqr with
    | inl hq =>
      have hpq : p ∧ q := And.intro hp hq
      exact (Or.inl hpq : (p ∧ q) ∨ (p ∧ r))
    | inr hr =>
      have hpq : p ∧ r := And.intro hp hr
      exact (Or.inr hpq : (p ∧ q) ∨ (p ∧ r))
  . intro (hpqpr : (p ∧ q) ∨ (p ∧ r))
    cases hpqpr with
    | inl hpq  =>
      have hp : p := And.left hpq
      have hq : q := And.right hpq
      have hqr : q ∨ r := Or.inl hq
      exact (And.intro hp hqr : p ∧ (q ∨ r))
    | inr hpr =>
      have hp : p := And.left hpr
      have hr : r := And.right hpr
      have hqr : q ∨ r := Or.inr hr
      exact (And.intro hp hqr : p ∧ (q ∨ r))

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro (hpqr : p ∧ (q ∨ r))
    cases And.right hpqr with
    | inl hq =>
      apply Or.inl
      . apply And.intro
        exact And.left hpqr
        exact hq
    | inr hr =>
      apply Or.inr
      . apply And.intro
        exact And.left hpqr
        exact hr
  . intro (hpqpr : (p ∧ q) ∨ (p ∧ r))
    cases hpqpr with
    | inl hpq =>
      apply And.intro
      . exact And.left hpq
      . exact (Or.inl (And.right hpq))
    | inr hpr =>
      apply And.intro
      . exact hpr.left
      . exact (Or.inr (And.right hpr))

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro (hpqr : p ∧ (q ∨ r))
    apply Or.elim hpqr.right
    . intro (hq : q)
      exact Or.inl (And.intro hpqr.left hq)
    . intro (hr : r)
      exact Or.inr (And.intro hpqr.left hr)
  . intro (hpqpr : (p ∧ q) ∨ (p ∧ r))
    apply Or.elim hpqpr
    . intro (hpq : p ∧ q)
      exact And.intro hpq.left (Or.inl hpq.right)
    . intro (hpr : p ∧ r)
      exact And.intro hpr.left (Or.inr hpr.right)


------------------------------------------------------------------------------------------------------------
/-
p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r)

1  |_ p ∨ (q ∧ r)
2  |  |_ p
3  |  |  p ∨ q                                Or.inl 2
4  |  |  p ∨ r                                Or.inl 2
5  |  |  (p ∨ q) ∧ (p ∨ r)                    And.intro 3,4
`
6  |  |_ q ∧ r
7  |  |  q                                    And.left 6
8  |  |  r                                    And.right 6
9  |  |  p ∨ q                                Or.inr 7
10 |  |  p ∨ r                                Or.inr 8
11 |  |  (p ∨ q) ∧ (p ∨ r)                    And.intro 8,9
12 |  (p ∨ q) ∧ (p ∨ r)                       Or.elim 1, 2-5, 6-11
13 p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r)            Conditional proof 1-12

14 |_ (p ∨ q) ∧ (p ∨ r)
15 |  p ∨ q                                   And.left 14
16 |  |_ p
17 |  |  p ∨ (q ∧ r)                          Or.inl 16

18 |  |_ q
19 |  |  p ∨ r                                And.right 14
20 |  |  |_ p
21 |  |  |  p ∨ (q ∧ r)                       Or.inl 21

22 |  |  |_ r
23 |  |  |  q ∧ r                             And.intro 18,22
24 |  |  |  p ∨ (q ∧ r)                       Or.inr 23
25 |  |  p ∨ (q ∧ r)                          Or.elim 19, 20-21, 22-24
26 |  p ∨ (q ∧ r)                             Or.elim 15, 16-17, 18-25
27 (p ∨ q) ∧ (p ∨ r) → p ∨ (q ∧ r)            Conditional proof 14-26

28 p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r)            Iff.intro 13,27
-/
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  . intro (hpqr : p ∨ (q ∧ r))
    cases hpqr with
    | inl hp =>
      have hpq : p ∨ q := Or.inl hp
      have hpr : p ∨ r := Or.inl hp
      exact (And.intro hpq hpr : (p ∨ q) ∧ (p ∨ r))
    | inr hqr =>
      have hq : q := And.left hqr
      have hr : r := And.right hqr
      have hpq : p ∨ q := Or.inr hq
      have hpr : p ∨ r := Or.inr hr
      exact (And.intro hpq hpr : (p ∨ q) ∧ (p ∨ r))
  . intro (hpqpr : (p ∨ q) ∧ (p ∨ r))
    have hpq : p ∨ q := And.left hpqpr
    cases hpq with
    | inl hp =>
      exact (Or.inl hp : p ∨ (q ∧ r))
    | inr hq =>
      have hpr : p ∨ r := And.right hpqpr
      cases hpr with
      | inl hp =>
        exact (Or.inl hp : p ∨ (q ∧ r))
      | inr hr =>
        have hqr : q ∧ r := And.intro hq hr
        exact (Or.inr hqr : p ∨ (q ∧ r))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  . intro hpqr
    cases hpqr with
    | inl hp =>
      exact ⟨(Or.inl hp), (Or.inl hp)⟩
    | inr hqr =>
      cases hqr with
      | intro hq hr =>
        exact ⟨(Or.inr hq), (Or.inr hr)⟩
  . intro hpqpr
    cases hpqpr with
    | intro hpq hpr =>
      cases hpq with
      | inl hp =>
        exact Or.inl hp
      | inr hq =>
        cases hpr with
        | inl hp' =>
          exact Or.inl hp'
        | inr hr =>
          exact Or.inr ⟨hq, hr⟩

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  . intro hpqr
    match hpqr with
    | Or.inl (hp : p) =>
      exact ⟨(Or.inl hp), (Or.inl hp)⟩
    | Or.inr (hqr : q ∧ r) =>
      exact match hqr with
      | ⟨hq, hr⟩ =>
        ⟨(Or.inr hq), (Or.inr hr)⟩
  . intro hpqpr
    match hpqpr with
    | ⟨hpq, hpr⟩ =>
      match hpq with
      | Or.inl hp =>
        exact Or.inl hp
      | Or.inr (hq : q) =>
        match hpr with
        | Or.inl hp' =>
          exact Or.inl hp'
        | Or.inr (hr : r) =>
          exact Or.inr ⟨hq, hr⟩

-- ###########################################################################################################
-- ## other properties
/-
(p → (q → r)) ↔ (p ∧ q → r)

1  |_ p → (q → r)
2  |  |_ p ∧ q
3  |  |  p                        And.left 2
4  |  |  q                        And.right 2
5  |  |  q → r                    Apply 1,3
6  |  |  r                        Apply 5,4
7  |  p ∧ q → r                   Conditional proof 2-6
8  p → (q → r) → (p ∧ q → r)      Conditional proof 1-7

9  |_ p ∧ q → r
10 |  |_ p
11 |  |  |_ q
12 |  |  |  p ∧ q                  And.intro 10,11
13 |  |  |  r                      Apply 9,12
14 |  |  q → r                     Conditional proof 11-13
15 |  p → (q → r)                  Conditional proof 10-14
16 (p ∧ q → r) → p → (q → r)       Conditional proof 9-15

17 (p → (q → r)) ↔ (p ∧ q → r)     Iff.intro 8,16
-/
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  apply Iff.intro
  . intro (hpqr : p → (q → r))
    intro (hpq : p ∧ q)
    have hp : p := And.left hpq
    have hq : q := And.right hpq
    have hqr : q → r := hpqr hp
    exact (hqr hq : r)
  . intro (hpqr : p ∧ q → r)
    intro (hp : p)
    intro (hq : q)
    have hpq : p ∧ q := And.intro hp hq
    exact (hpqr hpq : r)

example : (p → (q → r)) ↔ (p ∧ q → r) := by
  apply Iff.intro
  . intro (hpqr : p → (q → r))
    intro (hpq : p ∧ q)
    cases hpq with
    | intro hp hq =>
      exact hpqr hp hq
  . intro (hpqr : p ∧ q → r)
    intro (hp : p)
    intro (hq : q)
    apply hpqr
    exact And.intro hp hq


----------------------------------------------------------------------------------------------------------
/-
((p ∨ q) → r) ↔ (p → r) ∧ (q → r)

1  |_ (p ∨ q) → r
2  |  |_ p
3  |  |  p ∨ q                          Or.inl 2
4  |  |  r                              Apply 1,3
5  |  p → r                             Conditional proof 2-4
6  |  |_ q
7  |  |  p ∨ q                          Or.inr 6
8  |  |  r                              Apply 1,7
9  |  q → r                             Conditional proof 6-8
10 |  (p → r) ∧ (q → r)                 And.intro 5,9
11 ((p ∨ q) → r) → (p → r) ∧ (q → r)    Conditional proof 1-10 (Watch out for the parentheses, as implication is right associative)

12 |_ (p → r) ∧ (q → r)
13 |  |_ p ∨ q
14 |  |  |_ p
15 |  |  |  p → r                       And.left 12
16 |  |  |  r                           Apply 15,14

17 |  |  |_ q
18 |  |  |  q → r                       And.right 12
19 |  |  |  r                           Apply 18,17
20 |  |  r                              Or.elim 13, 14-16, 17-19
21 |  p ∨ q → r                         Conditional proof 13-20
22 (p → r) ∧ (q → r) → ((p ∨ q) → r)    Conditional proof 12-21

23 ((p ∨ q) → r) ↔ (p → r) ∧ (q → r)    Iff.intro 11,22
-/
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  apply Iff.intro
  . intro (hpqr : (p ∨ q) → r)
    apply And.intro
    . intro (hp : p)
      have hpq : p ∨ q := Or.inl hp
      exact (hpqr hpq : r)
    . intro (hq : q)
      have hpq : p ∨ q := Or.inr hq
      exact (hpqr hpq : r)
  . intro (hprqr : (p → r) ∧ (q → r))
    . intro (hpq : p ∨ q)
      cases hpq with
      | inl hp =>
        have hpr : p → r := And.left hprqr
        exact (hpr hp : r)
      | inr hq =>
        have hqr : q → r := And.right hprqr
        exact (hqr hq : r)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  constructor
  · intro h
    constructor
    · intro hp
      exact h (Or.inl hp)
    · intro hq
      exact h (Or.inr hq)
  · intro h hpq
    cases hpq with
    | inl hp => exact h.left hp
    | inr hq => exact h.right hq


-----------------------------------------------------------------------------------------------------------
/-
¬(p ∨ q) ↔ ¬p ∧ ¬q

1  |_ ¬(p ∨ q)
2  |  |_ p
3  |  |  p ∨ q                Or.inl 2
4  |  |  False                Apply 1,3
5  |  p → False               Conditional proof 2-4
6  |  ¬ p                     ¬ Definition 5

7  |  |_ q
8  |  |  p ∨ q                Or.inr 7
9  |  |  False                Apply 1,8
10 |  q → False               Conditional proof 7-9
11 |  ¬ q                     ¬ Definition 10
12 |  ¬p ∧ ¬q                 And.intro 6,11
13 ¬(p ∨ q) → ¬p ∧ ¬q         Conditional proof 1-12

14 |_ ¬p ∧ ¬q
15 |  |_ p ∨ q
16 |  |  |_ p
17 |  |  |  ¬p                And.left 14
18 |  |  |  False             Apply 17,16

19 |  |  |_ q
20 |  |  |  ¬q                And.right 14
21 |  |  |  False             Apply 20,19
22 |  |  False                Or.elim 15, 16-18, 19-21
23 | (p ∨ q) → False          Conditional proof 15-22
24 | ¬ (p ∨ q)                ¬ Definition 24
25 ¬p ∧ ¬q → ¬(p ∨ q)         Conditional proof 14-24

26 ¬(p ∨ q) ↔ ¬p ∧ ¬q         Iff.intro 13,25
-/
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  apply Iff.intro
  . intro (hnpq : ¬(p ∨ q))
    have hpFalse : p → False := by
      intro (hp : p)
      have hpq : p ∨ q := Or.inl hp
      exact (hnpq hpq : False)
    have hnp : ¬p := hpFalse             -- ¬ Definition
    have hqFalse : q → False := by
      intro (hq : q)
      have hpq : p ∨ q := Or.inr hq
      exact (hnpq hpq : False)
    have hnq : ¬q := hqFalse             -- ¬ Definition
    exact And.intro hnp hnq
  . intro (hnpnq : ¬p ∧ ¬q)
    . intro (hpq : p ∨ q)
      cases hpq with
      | inl hp =>
        have hnp : ¬p := And.left hnpnq
        exact (hnp hp : False)
      | inr hq =>
        have hnq : ¬q := And.right hnpnq
        exact (hnq hq : False)

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  apply Iff.intro
  . intro (hnpq : ¬(p ∨ q))
    apply And.intro
    . intro (hp : p)
      exact hnpq (Or.inl hp)
    . intro (hq : q)
      exact hnpq (Or.inr hq)
  . intro (hnpnq : ¬p ∧ ¬q)
    . intro (hpq : p ∨ q)
      cases hpq with
      | inl hp =>
        exact (And.left hnpnq) hp
      | inr hq =>
        exact (And.right hnpnq) hq


------------------------------------------------------------------------------------------------
/-
¬p ∨ ¬q → ¬(p ∧ q)

1  |_ ¬p ∨ ¬q
2  |  |_ p ∧ q
3  |  |  |_ ¬p
4  |  |  |  p           And.left 2
5  |  |  |  False       Apply 3,4

6  |  |  |_ ¬q
7  |  |  |  q           And.right 2
8  |  |  |  False       Apply 6,7
9  |  |  False          Or.elim 1, 3-5, 6-8
10 | (p ∧ q) → False    Conditional proof 2-9
11 | ¬(p ∧ q)           ¬ Definition 10
12 ¬p ∨ ¬q → ¬(p ∧ q)   Conditional proof 1-11
-/
example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro (hnpnq : ¬p ∨ ¬q)
  intro (hpq : p ∧ q)
  cases hnpnq with
  | inl hnp =>
    have hp : p := And.left hpq
    exact (hnp hp : False)
  | inr hnq =>
    have hq : q := And.right hpq
    exact (hnq hq : False)

example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro (hnpnq : ¬p ∨ ¬q)
  intro (hpq : p ∧ q)
  cases hnpnq with
  | inl hnp =>
    cases hpq with
    | intro hp =>
      exact hnp hp
  | inr hnq =>
    cases hpq with
    | intro hp hq =>
      exact hnq hq


-------------------------------------------------------------------------------------------------------
/-
¬(p ∧ ¬p)

1  |_ p ∧ ¬p
2  |  p                And.left 1
3  |  ¬p               And.right 1
4  |  False            Apply 3,2
5  (p ∧ ¬p) → False    Conditional proof 1-4
6  ¬(p ∧ ¬p)           ¬ Definition 5
-/
example : ¬(p ∧ ¬p) := by
  intro (hpnp : p ∧ ¬p)
  have hp : p := And.left hpnp
  have hnp : ¬p := And.right hpnp
  exact (hnp hp : False)

example : ¬(p ∧ ¬p) := by
  intro (hpnp : p ∧ ¬p)
  exact And.right hpnp (And.left hpnp)

example : ¬(p ∧ ¬p) := by
  intro (hpnp : p ∧ ¬p)
  cases hpnp with
  | intro hp hnp =>
    exact hnp hp


---------------------------------------------------------------------------------------------
/-
p ∧ ¬q → ¬(p → q)

1  |_ p ∧ ¬q
2  |  p                And.left 1
3  |  ¬q               And.right 1
4  |  |_ p → q
5  |  |  q             Apply 4,2
6  |  |  False         Apply 3,5
7  |  (p → q) → False  Conditional proof 4-6
8  |  ¬(p → q)         ¬ Definition 7
9  p ∧ ¬q → ¬(p → q)   Conditional proof 1-7
-/
example : p ∧ ¬q → ¬(p → q) := by
  intro (hpnpq : p ∧ ¬q)
  have hp : p := hpnpq.left
  have hnpq : ¬q := hpnpq.right
  . intro (hpq : p → q)
    have hq : q := hpq hp
    exact (hnpq hq : False)


----------------------------------------------------------------------------------------------
/-
¬p → (p → q)

1  |_ ¬p
2  |  |_ p
3  |  |  False              Apply 1,2
4  |  |  q                  False.elim 3 (Ex falso quodlibet,'q'  deduced from False.)
5  |  p → q                 Conditional proof: 2-4
6  ¬p → (p → q)             Conditional proof: 1-5
-/
example : ¬p → (p → q) := by
  intro (hnp : ¬p)
  intro (hp : p)
  have false : False := hnp hp
  exact (False.elim false : q)

example : ¬p → (p → q) := by
  intro (hnp : ¬p)
  intro (hp : p)
  have : False := hnp hp
  exact (False.elim this : q)

example : ¬p → (p → q) := by
  intros hnp hp
  contradiction

-- Using 'absurd'.
example : ¬p → (p → q) := by
  intro (hnp : ¬p)
  intro (hp : p)
  exact (absurd hp hnp : q)


---------------------------------------------------------------------------------------------
-- Example: How to prove that 42 = 7 from False?
/-
False → 42 = 7 means: "If False is true, then 42 = 7."

1  |_ False
2  |  42 = 7              False.elim 1
3  False → 42 = 7         Conditional proof: 1-2
-/
example : False → 42 = 7 := by
  intro (hFalse : False)
  exact (False.elim hFalse : 42 = 7)


----------------------------------------------------------------------------------------------
/-
(¬p ∨ q) → (p → q)

1  |_ ¬p ∨ q
2  |  |_ p
3  |  |  |_ ¬p
4  |  |  |  False              Apply 3,2
5  |  |  |  q                  False.elim 4

6  |  |  |_ q
7  |  |  |  q                  Reiteration 6
8  |  |  q                     Or.elim 1, 3-5, 6-7
9  |  p → q                    Conditional proof 2-8
10 (¬p ∨ q) → (p → q)          Conditional proof 1-9
-/
example : (¬p ∨ q) → (p → q) := by
  intro (hnpq : ¬p ∨ q)
  intro (hp : p)
  cases hnpq with
  | inl hnp =>
    have false : False := hnp hp
    exact False.elim false
  | inr hq =>
    exact hq


----------------------------------------------------------------------------------------------
/-
p ∨ False ↔ p

1  |_ p ∨ False
2  |  |_ p
3  |  |  p              Reiteration 2

4  |  |_ False
5  |  |  p              False.elim 4
6  |  p                 Or.elim 1, 2-3, 4-5
7  |  p ∨ False → p     Conditional proof 1-7

8  |_ p
9  |  p ∨ False         Or.inl 8
10 p → p ∨ False        Conditional proof 8-9

11 p ∨ False ↔ p        Iff.intro 7,10
-/
example : p ∨ False ↔ p := by
  apply Iff.intro
  intro (hpFalse : p ∨ False)
  . cases hpFalse with
    | inl hp =>
      exact (hp : p)
    | inr hFalse =>
      exact (False.elim hFalse : p)
  intro (hp : p)
  . exact (Or.inl hp : p ∨ False)


---------------------------------------------------------------------------------------------
/-
p ∧ False ↔ False

1  |_ p ∧ False
2  |  False                    And.right 1
3  p ∧ False → False           Conditional proof 1-2

4  |_ False
5  |  p                        False.elim 5
6  |  p ∧ False                And.intro 5,4
7  False → p ∧ False           Conditional proof: 4-6

8  p ∧ False ↔ False           Iff.intro: 3,7
-/
example : p ∧ False ↔ False := by
  apply Iff.intro
  intro (hpFalse : p ∧ False)
  . exact (And.right hpFalse : False)
  intro (hFalse : False)
  . have : p := False.elim hFalse
    exact (And.intro this hFalse : p ∧ False)


---------------------------------------------------------------------------------------------
/-
(p → q) → (¬q → ¬p)

1  |_ p → q
2  |  |_ ¬q
3  |  |  |_ p
4  |  |  |  q                   Apply 1,3
5  |  |  |  False               Apply 2,4
6  |  |  p → False              Conditional proof 3-5
7  |  |  ¬p                     ¬ Definition 6
8  |  ¬q → ¬p                   Conditional proof 2-7
9  (p → q) → (¬q → ¬p)          Conditional proof 1-8
-/
example : (p → q) → (¬q → ¬p) := by
  intro (hpq : p → q)
  . intro (hnq : ¬q)
    . intro (hp : p)
      have hq : q := hpq hp
      exact (hnq hq : False)


-- #############################################################################################
-- ## Prove the following identities, replacing the sorry placeholders with actual proofs.
-- These require classical reasoning.
open Classical

--------------------------------------------------------------------------------------------
/-
(p → q ∨ r) → ((p → q) ∨ (p → r))

1  |_ p → q ∨ r
2  |  p ∨ ¬p                            Excluded middle p
3  |  |_ p
4  |  |  q ∨ r                          Apply 1,3
6  |  |  |_ q
7  |  |  |  |_ p
8  |  |  |  |  q                        Reiteration 6
9  |  |  |  p → q                       Conditional proof 7-8
10 |  |  |  (p → q) ∨ (p → r)           Or.inl

11 |  |  |_ r
12 |  |  |  |_ p
13 |  |  |  |  r                        Reiteration 11
14 |  |  |  p → r                       Conditional proof 12-13
15 |  |  |  (p → q) ∨ (p → r)           Or.inr
16 |  |  (p → q) ∨ (p → r)              Or.elim 4, 6-10, 11-15

17 |  |_ ¬p
18 |  |  |_ p
19 |  |  |  False                       Apply 17,18
20 |  |  |  q                           False.elim 19
21 |  |  p → q                          Conditional proof 18-20
22 |  |  (p → q) ∨ (p → r)              Or.inl 21
23 |  (p → q) ∨ (p → r)                 Or.elim 2, 3-16, 17-22
24 (p → q ∨ r) → ((p → q) ∨ (p → r))    Conditional proof 1-23
-/
example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro (hpqr : p → q ∨ r)
  . cases Classical.em p with
    | inl hp =>
      have hqr : q ∨ r := hpqr hp
      cases hqr with
      | inl hq =>
        have hpq : p → q := by
          intro (hp : p)
          exact hq
        exact (Or.inl hpq : (p → q) ∨ (p → r))
      | inr hr =>
        have hpr : p → r := by
          intro (hp : p)
          exact (hr : r)
        exact (Or.inr hpr : (p → q) ∨ (p → r))
    | inr hnp =>
      have hpq : p → q := by
        intro (hp : p)
        have hFalse : False := hnp hp
        exact (False.elim hFalse : q)
      exact (Or.inl hpq : (p → q) ∨ (p → r))

/-
(p → q ∨ r) → ((p → q) ∨ (p → r))

1  |_ p → q ∨ r
2  |  (p → q) ∨ ¬(p → r)              Excluded middle (p → q)
3  |  |_ p → q
4  |  |  (p → q) ∨ (p → r)            Or.inl 3

5  |  |_ ¬(p → q)
6  |  |  |_ p
7  |  |  |  q ∨ r                     Apply 1,6
8  |  |  |  |_ q
9  |  |  |  |  |_ p
10 |  |  |  |  |  q                   Reiteration 8
11 |  |  |  |  p → q                  Conditional proof 9-10
12 |  |  |  |  False                  Apply 5,11
13 |  |  |  |  r                      False.elim 12

14 |  |  |  |_ r
15 |  |  |  |  r                      Reiteration 14
16 |  |  |  r                         Or.elim 7, 8-13, 14-15
17 |  |  p → r                        Conditional proof 6-16
18 |  |  (p → q) ∨ (p → r)            Or.inr 17
19 |  (p → q) ∨ (p → r)               Or.elim 2, 3-4, 5-18
20 (p → q ∨ r) → ((p → q) ∨ (p → r))  Conditional proof 1,19
-/
example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro (hpqr : p → q ∨ r)
  cases Classical.em (p → q) with
  | inl hpq =>
    exact (Or.inl hpq : (p → q) ∨ (p → r))
  | inr hnpq =>
    have hpr : p → r := by
      intro (hp : p)
      have hqr : q ∨ r := hpqr hp
      cases hqr with
      | inl hq =>
        have hFalse : False := by
          have hpq : p → q := by
            intro (hp : p)
            exact hq
          exact (hnpq hpq : False)
        exact (False.elim hFalse : r)
      | inr hr =>
        exact hr
    exact (Or.inr hpr : (p → q) ∨ (p → r))

-- Simpler version.
example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro hpqr
  cases Classical.em (p → q) with
  | inl hpq =>
    exact Or.inl hpq
  | inr hnpq =>
    have hpr : p → r := by
      intro hp
      cases hpqr hp with
      | inl hq => exact False.elim (hnpq (fun _ => hq))
      | inr hr => exact hr
    exact Or.inr hpr

-- Using 'suffices'.
example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro hpqr
  cases Classical.em (p → q) with
  | inl hpq => exact Or.inl hpq
  | inr hnpq =>
    suffices hpr : p → r from Or.inr hpr
    . intro hp
      cases hpqr hp with
      | inl hq => exact False.elim (hnpq (fun _ => hq))
      | inr hr => exact hr

-- Using 'refine'.
example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro hpqr
  cases Classical.em (p → q) with
  | inl hpq => exact Or.inl hpq
  | inr hnpq =>
    refine Or.inr
      (fun hp =>
       match hpqr hp with
       | Or.inl hq => False.elim (hnpq (fun _ => hq))
       | Or.inr hr => hr)


-------------------------------------------------------------------------------------------
/-
¬(p ∧ q) → ¬p ∨ ¬q

1  |_ ¬(p ∧ q)
3  |  p ∨ ¬p                   Excluded middle p
4  |  |_ p
5  |  |  |_ q
6  |  |  |  p ∧ q              And.intro 4,5
7  |  |  |  False              Apply 1,6
8  |  |  q → False             Conditional proof 5-7
9  |  |  ¬q                    ¬ Definition 8
10 |  |  ¬p ∨ ¬q               Or.inr 9

11 |  |_ ¬p
12 |  |  ¬p ∨ ¬q               Or.inl 11
13 |  ¬p ∨ ¬q                  Or.elim 3, 4-10, 11-12
14 ¬(p ∧ q) → ¬p ∨ ¬q          Conditional proof 1-13
-/
example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro (hnpq : ¬(p ∧ q))
  cases Classical.em p with
  | inl hp =>
    have hnq : ¬q := by
      intro (hq : q)
      have hpq : p ∧ q := And.intro hp hq
      exact (hnpq hpq : False)
    exact (Or.inr hnq : ¬p ∨ ¬q)
  | inr hnp =>
    exact (Or.inl hnp : ¬p ∨ ¬q)

/-
¬(p ∧ q) → ¬p ∨ ¬q

1  |_ ¬(p ∧ q)
3  |  p ∨ ¬p                   Excluded middle p
4  |  |_ p
5  |  |  q ∨ ¬q                Excluded middle q
6  |  |  |_ q
7  |  |  |  p ∧ q              And.intro 4,5
8  |  |  |  False              Apply 1,6
9  |  |  |  ¬p ∨ ¬q            False.elim 8

10 |  |  |_ ¬q
11 |  |  |  ¬p ∨ ¬q            Or.inr 10
12 |  |  ¬p ∨ ¬q               Or.elim 5, 7-9, 10-11

13 |  |_ ¬p
14 |  |  ¬p ∨ ¬q               Or.inl 13
15 |  ¬p ∨ ¬q                  Or.elim 3, 4-12, 13-14
16 ¬(p ∧ q) → ¬p ∨ ¬q          Conditional proof 1-15
-/
example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro (hnpq : ¬(p ∧ q))
  cases Classical.em p with
  | inl hp =>
    cases Classical.em q with
    | inl hq =>
      have hpq : (p ∧ q) := And.intro hp hq
      have hFalse : False := hnpq hpq
      exact (False.elim hFalse : ¬p ∨ ¬q)
    | inr hnq =>
      exact (Or.inr hnq)
  | inr hnp =>
    exact Or.inl hnp


---------------------------------------------------------------------------------------------------------------------------------------------------
-- An example that requires classical reasoning (this is not included in the examples of propositional validities, contrary to what the book says).
/-
¬(p ∧ ¬q) → (p → q)

1  |_ ¬(p ∧ ¬q)
2  |  |_ p
3  |  |  q ∨ ¬q             Excluded middle q
4  |  |  |_ q
5  |  |  |  q               Reiteration 4

6  |  |  |_ ¬q
7  |  |  |  p ∧ ¬q          And.intro 2 6
8  |  |  |  False           Apply 1,7
9  |  |  |  q               False.elim 8
10 |  |  q                  Or.elim 3, 4-5, 6-9
11 | p → q                  Conditional Proof 2-10
12 ¬(p ∧ ¬q) → (p → q)      Conditional Proof 1-11
-/
example (p q : Prop) : ¬(p ∧ ¬q) → (p → q) := by
  intro (hnpnq : ¬(p ∧ ¬q))
  intro (hp : p)
  cases Classical.em q with
  | inl hq =>
    exact hq
  | inr hnq =>
    have hpq : p ∧ ¬q := And.intro hp hnq
    have hFalse : False := hnpnq hpq
    exact (False.elim hFalse : q)


------------------------------------------------------------------------------------------------
/-
¬(p → q) → p ∧ ¬q

1  |_ ¬(p → q)
2  |  p ∨ ¬p                  Excluded middle p
3  |  |_ p
4  |  |  |_ q
5  |  |  |  |_ p
6  |  |  |  |  q              Reiteration 4
7  |  |  |  p → q             Conditional proof 5-6
8  |  |  |  False             Apply 1,7
9  |  |  q → False            Conditional proof 4-8
10 |  |  ¬q                   ¬ Definition 9
11 |  |  p ∧ ¬q               And.intro 3,10

12 |  |_ ¬p
13 |  |  |_ p
14 |  |  |  False             Apply 12,13
15 |  |  |  q                 False.elim 14
16 |  |  p → q
17 |  |  False                Apply 1,16
18 |  |  p ∧ ¬q               False.elim 12
19 |  p ∧ ¬q                  Or.elim 2, 3-11, 12-18
20 ¬(p → q) → p ∧ ¬q          Conditional proof 1-19
-/
example : ¬(p → q) → p ∧ ¬q := by
  intro (hnpq : ¬(p → q))
  cases Classical.em p with
  | inl hp =>
    have hnq : ¬q := by
      intro (hq : q)
      have hpq : p → q := by
        intro (hp : p)
        exact hq
      exact (hnpq hpq : False)
    exact (And.intro hp hnq : p ∧ ¬q)
  | inr hnp =>
    have hpq : p → q := by
      intro (hp : p)
      have hFalse : False := hnp hp
      exact (False.elim hFalse : q)
    have hFalse : False := hnpq hpq
    exact (False.elim hFalse : p ∧ ¬q)


/--
byContradiction is equivalent to Double Negation Elimination (DNE) or to Excluded Middle (EM).

¬(p → q) → p ∧ ¬q

1  |_ ¬(p → q)
2  |  |_ ¬p
3  |  |  |_ p
4  |  |  |  False         Apply 2,3
5  |  |  |  q             False.elim 4 (equivalent to 'absurd 3,2')
6  |  |  p → q            Conditional proof 3-5
7  |  |  False            Apply 1,6
8  |  p                   ByContradiction 2-7
9  |  |_ q
10 |  |  |_ p
11 |  |  |  q
12 |  |  p → q            Conditional proof 10-11
11 |  |  False            Apply 1,12
12 |  q → False           Conditional proof 9-11
13 |  ¬q                  ¬ Definition 12
14 |  p ∧ ¬q              And.intro 8,13
15 ¬(p → q) → p ∧ ¬q      Conditional proof 1-14
-/
example : ¬(p → q) → p ∧ ¬q := by
  intro (hnpq : ¬(p → q))
  have hp : p :=
    byContradiction (by   -- byContradiciton is equivalent to Double Negation Elimination (DNE)
      intro hnp
      have hpq : p → q := by
        intro (hp : p)
        have hFalse : False := hnp hp
        exact (False.elim hFalse : q)
      exact (hnpq hpq : False))
  have hnq : ¬q := by
    intro (hq : q)
    have hpq : p → q := by
      intro (hp : p)
      exact hq
    exact (hnpq hpq : False)
  exact (And.intro hp hnq : p ∧ ¬q)


--------------------------------------------------------------------------------------------------------
/-
(p → q) → (¬p ∨ q)

1  |_ p → q
2  |  p ∨ ¬p                 Excluded Middle (em p)
3  |  |_ p
4  |  |  q                   Apply 1,3
5  |  |  ¬p ∨ q              Or.inr 4

6  |  |_ ¬p
7  |  |  ¬p ∨ q              Or.inl 6
8  |  ¬p ∨ q                 Or.elim 2, 3-5, 6-7
9  (p → q) → (¬p ∨ q)        Conditional proof 1-8
-/
example : (p → q) → (¬p ∨ q) := by
  intro (hpq : p → q)
  cases Classical.em p with
  | inl hp =>
    have hq : q := hpq hp
    exact (Or.inr hq : ¬p ∨ q)
  | inr hnp =>
    exact (Or.inl hnp : ¬p ∨ q)

/-
(p → q) → (¬p ∨ q)

1  |_ p → q
2  |  p ∨ ¬p                Excluded Middle (em p)
3  |  |_ p
4  |  |  |_ ¬q
5  |  |  |  q               Apply 1,3
6  |  |  |  False           Apply 4,5
7  |  |  ¬q → False         Conditional proof 4-6
8  |  |  q                  ByContradiction 7 (Double Negation Elimination)
9  |  |  ¬p ∨ q             Or.inr 8

10 |  |_ ¬p
11 |  |  ¬p ∨ q             Or.inl 10
12 |  ¬p ∨ q                Or.elim 2, 3-9, 10-11
13 (p → q) → (¬p ∨ q)       Conditional proof 1-12
-/
example : (p → q) → (¬p ∨ q) := by
  intro (hpq : p → q)
  cases Classical.em p with
  | inl hp =>
    have hnqFalse : ¬q → False := by
      intro (hnq : ¬q)
      have hq : q := hpq hp
      exact (hnq hq : False)
    have hq : q := Classical.byContradiction hnqFalse
    exact (Or.inr hq)
  | inr hnp =>
    exact (Or.inl hnp)


----------------------------------------------------------------------------------------------------------
/-
(¬q → ¬p) → (p → q)

1  |_ ¬q → ¬p
2  |  |_ p
3  |  |  q ∨ ¬q          Excluded Middle (em q)
4  |  |  |_ q
5  |  |  |  q            Reiteration 4

6  |  |  |_ ¬q
7  |  |  |  ¬p           Apply 1,6
8  |  |  |  q            Absurd 2,7
9  |  |  q               Or.elim 3, 4-5, 6-8
10 |  p → q              Conditional proof 2-9
11 (¬q → ¬p) → (p → q)   Conditional proof 1-10
-/
example : (¬q → ¬p) → (p → q) := by
  intro (hnqnp : ¬q → ¬p)
  . intro (hp : p)
    cases Classical.em q with
    | inl hq =>
      exact hq
    | inr hnq =>
      have hnp : ¬p := hnqnp hnq
      exact (absurd hp hnp : q)

/-
(¬q → ¬p) → (p → q)

1  |_ ¬q → ¬p
2  |  |_ p
3  |  |  p ∨ ¬p          Excluded Middle (em p)
4  |  |  |_ p
5  |  |  |  |_ ¬q
6  |  |  |  |  ¬p        Apply 1,5
7  |  |  |  |  False     Apply 6,2
8  |  |  |  ¬q → False   Conditional proof 5-7
9  |  |  |  q            ByContradiction 8

10 |  |  |_ ¬p
11 |  |  |  False        Apply 10,2
12 |  |  |  q            False.elim 11
13 |  |  q               Or.elim 3, 4-9, 10-12
14 |  p → q              Conditional proof 2-13
15 (¬q → ¬p) → (p → q)   Conditional proof 1-14
-/
example : (¬q → ¬p) → (p → q) := by
 intro (hnqnp : ¬q → ¬p)
 .  intro (hp : p)
    cases Classical.em p with
    | inl hp =>
      have hnqFalse : ¬q → False := by
        intro (hnq : ¬q)
        have hnp : ¬p := hnqnp hnq
        exact (hnp hp : False)
      exact byContradiction hnqFalse
    | inr hnp =>
      have hFalse : False := hnp hp
      exact (False.elim hFalse : q)


-----------------------------------------------------------------------------------------------------------
/-
p ∨ ¬p

1 p ∨ ¬p  Excluded Middle (em p)
-/
example : p ∨ ¬p := by
  exact Classical.em p

example : p ∨ ¬p := by
  cases Classical.em p with
  | inl hp => exact Or.inl hp
  | inr hnp => exact Or.inr hnp


--------------------------------------------------------------------------------------------------------------
/-
(((p → q) → p) → p)

1  |_ (p → q) → p
2  |  p ∨ ¬p                Excluded Middle (em p)
3  |  |_ p
4  |  |  p                  Reiteration 3

5  |  |_ ¬p
6  |  |  |_ p
7  |  |  |  False           Apply 5,6
8  |  |  |  q               False.elim 8
9  |  |  p → q              Conditional proof 5-9
10 |  |  p                  Apply 1,9
11 (((p → q) → p) → p)      Conditional proof 1-10
-/
example : (((p → q) → p) → p) := by
  intro (hpqp : (p → q) → p)
  cases Classical.em p with
  | inl hp =>
    exact (hp : p)
  | inr hnp =>
    have hpq : p → q := by
      intro (hp : p)
      have hFalse : False := hnp hp
      exact (False.elim hFalse : q)
    exact (hpqp hpq : p)


example : (((p → q) → p) → p) := by
  intro (hpqp : (p → q) → p)
  cases Classical.em p with
  | inl hp =>
    exact (hp : p)
  | inr hnp =>
    have hpq : p → q := by
      intro (hp : p)
      contradiction
    exact (hpqp hpq : p)
/-
(((p → q) → p) → p)

1  p ∨ ¬p                       Excluded Middle (em p)
2  |  |_ p
3  |  |  |_ (p → q) → p
4  |  |  |  p                   Reiteration 2
5  |  |  ((p → q) → p) → q      Conditional proof 3-4

6  |  |_ ¬p
7  |  |  |_ (p → q) → p
8  |  |  |  |_ p
9  |  |  |  |  False            Apply 6,8
10 |  |  |  |  q                False.elim 9
11 |  |  |  p → q               Conditional proof 8-10
12 |  |  |  p                   Apply 7,11
13 |  |  (p → q) → p) → p       Conditional proof 7-12
14 |  ((p → q) → p) → p         Or.elim 1, 2-5, 6-13
-/
example : (((p → q) → p) → p) := by
  cases Classical.em p with
  | inl hp =>
    intro (hpqp : (p → q) → p)
    exact hp
  | inr hnp =>
      intro (hpqp : (p → q) → p)
      have hpq : p → q := by
        intro (hp : p)
        have hFalse : False := hnp hp
        exact (False.elim hFalse : q)
      exact (hpqp hpq : p)


------------------------------------------------------------------------------------------------
-- Prove ¬(p ↔ ¬p) without using classical logic.
/-
¬(p ↔ ¬p)

1  |_ p ↔ ¬p
2  |  |_ p
3  |  |  p → ¬p         Iff.mp 1
4  |  |  ¬p             Apply 2,3
5  |  |  False          Apply 3,2
6  |  p → False         Conditional proof 2-5
7  |  ¬p                ¬ Definition
8  |  ¬p → p            Iff.mpr 1
9  |  p                 Apply 8,7
10 |  False             Apply 7,9
11 (p ↔ ¬p) → False     Conditional proof 1-12
12 ¬ (p ↔ ¬p) → False   ¬ Definition 11
-/
example : ¬(p ↔ ¬p) := by
  intro (hpnq : p ↔ ¬p)
  have hpFalse : p → False := by
    intro (hp : p)
    have hpnp : p → ¬p := Iff.mp hpnq
    have hnp : ¬p := hpnp hp
    exact (hnp hp : False)
  have hnpFalse : ¬p → p := Iff.mpr hpnq
  have hnp : ¬p := hpFalse                -- ¬ Definition
  have hp : p := hnpFalse hnp
  exact (hpFalse hp : False)


-- 'let' and 'have' are interchangeable here.
example : ¬(p ↔ ¬p) := by
  intro (hpnq : p ↔ ¬p)
  let hpFalse : p → False := by
    intro (hp : p)
    let hpnp : p → ¬p := Iff.mp hpnq
    let hnp : ¬p := hpnp hp
    exact (hnp hp : False)
  let hnpfalse : ¬p → p := Iff.mpr hpnq
  let hnp : ¬p := hpFalse
  let hp : p := hnpfalse hnp
  exact (hpFalse hp : False)
