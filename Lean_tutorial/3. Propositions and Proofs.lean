
-- ## Notes
-- Use preferably the following.
-- And.intro for ∧ introduction.
-- And.left and And.right for ∧ elimination.
-- Or.inl and Or.inr for ∨ introduction.
-- Or.elim for ∨ elimination.

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
example : p → q → p :=
 fun hp : p =>
 fun hq : q => hp

example : p → q → p :=
  fun hp : p =>
  fun _ : q => hp

example : p → q → p :=
  fun hp : p =>
  fun _ : q =>
  show p from hp


---------------------------------------------------------------------------------------
/-
p ⊢ p or equivalently p : p

1  p
3  p  Reiteration
-/
theorem t1 (hp : p) : p := hp



---------------------------------------------------------------------------------------
/-
q ⊢ p → q

1  q
2  |_ p
3  |  q    Reiteration
4  q → p   Conditional proof 2-3
-/
example (hp : p) : q → p :=
  fun _ => hp

theorem t2 (hp : p) : q → p := fun (hq : q) => hp
theorem t3 (hp : p) : q → p := fun _ => hp

-------------------------------------------------------------------------------------------
-- Tactics Examples not in the book
/-
'False' is equivalent to '⊥'.
False.elim is equivalent to 'Ex falso quodlibet'.

¬p → p → q

1  |_ ¬p
2  |  |_ p
3  |  |  False    Apply 1,2
3  |  |  q        False.elim 3 (From 'False' we can derive anything, 'q' in this case)
4  |  p → q       Conditional proof 2-3
5  ¬p → p → q     Conditional proof 1-4
-/
example : ¬p → p → q :=
  fun hnp : ¬p =>
  fun hp : p =>
  show q from absurd hp hnp

example : ¬p → p → q :=
  fun hnp : ¬p =>
  fun hp : p =>
  show q from False.elim (hnp hp)

----------------------------------------------------------------------------------
-- Examples not in the book

/-
byContradiction is equivalent to Double Negation Elimination (DNE) or to Excluded Middle (EM).

¬¬p : p
-/
example (h : ¬¬p) : p :=
  Classical.byContradiction h

/-
¬¬p → p

1  |_ ¬¬p
2  |  p     byContradiction 1
3  ¬¬p → p  Conditional proof 1-2
-/
example : ¬¬p → p :=
  fun hnnp : ¬¬p =>
  Classical.byContradiction hnnp


/-
¬p, p ⊢ q

1  ¬p
2  p
3  False    Apply 1,2
4  q        False.elim 3
-/
example (hnp : ¬p) (hp : p) : q :=
  False.elim (hnp hp)

example (hnp : ¬p) (hp : p) : q :=
  absurd hp hnp


-------------------------------------------------------------------------------------------
/-
1  ¬p
2  |_ p
3  |  False   Apply 1,2
4  |  q       False.elim
5  p → q
-/
example (hnp : ¬p) : p → q :=
  fun hp : p =>
  False.elim (hnp hp)

example (hnp : ¬p) :  p → q :=
  fun hp : p =>
  absurd hp hnp


------------------------------------------------------------------------------------------------
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
example : ¬p → p → q :=
  fun hnp =>
  fun hp =>
  absurd hp hnp

example : ¬p → p → q :=
  fun hnp : ¬p =>
  fun hp : p =>
  False.elim (hnp hp)


----------------------------------------------------------------------------------------------------
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
example : (p → q) ∨ (q → p) :=
  Or.elim (Classical.em p)
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
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q => show q ∧ p from And.intro h.right h.left)
    (fun h : q ∧ p => show p ∧ q from And.intro h.right h.left)

example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h => And.intro h.right h.left)
    (fun h => And.intro h.right h.left)


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
example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h => Or.elim h
      (fun hp => Or.inr hp)
      (fun hq => Or.inl hq))
    (fun h => Or.elim h
      (fun hq => Or.inr hq)
      (fun hp => Or.inl hp))


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
15 |  p ∧ (q ∧ r) → (p ∧ q) ∧ r   Conditional proof 9-14

16 (p ∧ q) ∧ r ↔ p ∧ (q ∧ r)   Iff.intro 8, 15
-/
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun h => And.intro (h.left.left) (And.intro h.left.right h.right))
    (fun h => And.intro (And.intro h.left h.right.left) h.right.right)


----------------------------------------------------------------------------------------------------------
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
26 p ∨ (p ∨ q) → (p ∨ q) ∨ r  Conditional proof 14-25

27 (p ∨ q) ∨ r ↔ p ∨ (q ∨ r)     Iff.intro 13,26
-/
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun hpqr => Or.elim hpqr
      (fun hpq => Or.elim hpq
        (fun hp => Or.inl hp)
        (fun hq => Or.inr (Or.inl hq)))
      (fun hr => Or.inr (Or.inr hr)))
    (fun hpqr => Or.elim hpqr
      (fun hp => Or.inl (Or.inl hp))
      (fun hqr => Or.elim hqr
        (fun hq => Or.inl (Or.inr hq))
        (fun hr => Or.inr hr)))

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun hpqr : (p ∨ q) ∨ r =>
      (Or.elim hpqr
        (fun hpq => (Or.elim hpq
          (fun hp => (Or.inl hp : p ∨ (q ∨ r)))
          (fun hq => (Or.inr (Or.inl hq : q ∨ r) : p ∨ (q ∨ r)))
          : p ∨ (q ∨ r))
        : p ∨ q → p ∨ (q ∨ r))
        (fun hr => (Or.inr (Or.inr hr : q ∨ r) : p ∨ (q ∨ r))
        : r → p ∨ (q ∨ r))
      : p ∨ (q ∨ r))
    : (p ∨ q) ∨ r → p ∨ (q ∨ r))
    (fun hpqr : p ∨ (q ∨ r) => (Or.elim hpqr
      (fun hp => (Or.inl (Or.inl hp) : (p ∨ q) ∨ r)
      : p → (p ∨ q) ∨ r)
      (fun hqr =>
        (Or.elim hqr
          (fun hq => (Or.inl (Or.inr hq : p ∨ q) : (p ∨ q) ∨ r)
          : q → (p ∨ q) ∨ r)
          (fun hr => (Or.inr hr : (p ∨ q) ∨ r)
          : r → (p ∨ q) ∨ r)))
        : (p ∨ q) ∨ r)
    : p ∨ (q ∨ r) → (p ∨ q) ∨ r)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun hpqr : (p ∨ q) ∨ r =>
      show p ∨ (q ∨ r) from Or.elim hpqr
      (fun hpq =>
        show p ∨ (q ∨ r) from (Or.elim hpq
        (fun hp =>
          show p ∨ (q ∨ r) from Or.inl hp)
        (fun hq =>
          show p ∨ (q ∨ r) from Or.inr (Or.inl hq))))
      (fun hr =>
        show p ∨ (q ∨ r) from Or.inr (Or.inr hr)))
    (fun hpqr : p ∨ (q ∨ r) =>
      show (p ∨ q) ∨ r from Or.elim hpqr
      (fun hp =>
        show (p ∨ q) ∨ r from Or.inl (Or.inl hp))
      (fun hqr =>
        show (p ∨ q) ∨ r from Or.elim hqr
        (fun hq =>
          show (p ∨ q) ∨ r from Or.inl (Or.inr hq))
        (fun hr =>
          show (p ∨ q) ∨ r from Or.inr hr )))


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
14 |  |  p                               And.left 14
15 |  |  q                               And.right 15
16 |  |  q ∨ r                           Or.inl 15
17 |  |  p ∧ (q ∨ r)                     And.intro 14,16

18 |  |_ p ∧ r
19 |  |  p                               And.left 18
20 |  |  r                               And.right 18
21 |  |  q ∨ r                           Or.inr 20
22 |  |  p ∧ (q ∨ r)                     And.intro 19,21
23 |  p ∧ (q ∨ r)                        Or.elim 12, 13-17, 18-22
24 (p ∧ q) ∨ (p ∧ r) → p ∧ (q ∨ r)       Conditional proof 18-23

25 p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)      Iff.intro 11,24
-/
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun hpqr => Or.elim hpqr.right
      (fun hq => Or.inl (And.intro hpqr.left hq))
      (fun hr => Or.inr (And.intro hpqr.left hr)))
    (fun hpqpr => Or.elim hpqpr
      (fun hpq => And.intro hpq.left (Or.inl hpq.right))
      (fun hpr => And.intro hpr.left (Or.inr hpr.right)))


-------------------------------------------------------------------------------------------------------------------
/-
p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r)

1  |_ p ∨ (q ∧ r)
2  |  |_ p
3  |  |  p ∨ q                                 Or.inl 2
4  |  |  p ∨ r                                 Or.inl 2
5  |  |  (p ∨ q) ∧ (p ∨ r)                     And.intro 3,4
`
6  |  |_ q ∧ r
7  |  |  q                                     And.left 6
8  |  |  r                                     And.right 6
9  |  |  p ∨ q                                 Or.inr 7
10 |  |  p ∨ r                                 Or.inr 8
11 |  |  (p ∨ q) ∧ (p ∨ r)                     And.intro 8,9
12 |  (p ∨ q) ∧ (p ∨ r)                        Or.elim 1, 2-5, 6-12
13 |  p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r)          Conditional proof 1-12

14 |_ (p ∨ q) ∧ (p ∨ r)
15 |  p ∨ q                                    And.left 14
16 |  |_ p
17 |  |  p ∨ (q ∧ r)                           Or.inl 16

19 |  |_ q
20 |  |  p ∨ r                                 And.right 14
21 |  |  |_ p
22 |  |  |  p ∨ (q ∧ r)                        Or.inl 21

23 |  |  |_ r
24 |  |  |  q ∧ r                              And.intro 19 23
25 |  |  |  p ∨ (q ∧ r)                        Or.inr 24
26 |  |  p ∨ (q ∧ r)                           Or.elim 20, 21-22, 23-25
27 |  p ∨ (q ∧ r)                              Or.elim 14, 16-17, 19-26

27 (p ∨ (q ∧ r)) ↔ ((p ∨ q) ∧ (p ∨ r))         Iff.intro 13,27
-/
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (fun hpqr => Or.elim hpqr
      (fun hp => And.intro (Or.inl hp) (Or.inl hp))
      (fun hqr => And.intro (Or.inr (And.left hqr)) (Or.inr (And.right hqr))))
    (fun hpqpr => Or.elim (And.left hpqpr)
      (fun hp => Or.inl hp)
      (fun hq => Or.elim (And.right hpqpr)
        (fun hp => Or.inl hp)
        (fun hr => Or.inr (And.intro hq hr))))


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
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun hpqr pq => hpqr pq.left pq.right)
    (fun hpqr p q => hpqr ⟨p, q⟩)

example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun (hpqr : p → (q → r)) (pq : p ∧ q) => (hpqr pq.left) pq.right)
    (fun (hpqr : p ∧ q → r) (p : p) (q : q) => hpqr ⟨p, q⟩)

example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun hpqr => fun pq => (hpqr pq.left) pq.right)
    (fun hpqr => fun p => fun q => hpqr ⟨p, q⟩)

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
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun hpqr => And.intro
      (fun hp => hpqr (Or.inl hp))
      (fun hq => hpqr (Or.inr hq)))
    (fun hprqr => fun pq =>
      Or.elim pq
      (fun hp => show r from hprqr.left hp)
      (fun hq => show r from hprqr.right hq))


-------------------------------------------------------------------------------------------------------
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
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun hnpq => And.intro
      (fun hp => show False from hnpq (Or.inl hp))
      (fun hq => show False from hnpq (Or.inr hq)))
    (fun hnpnq =>
      fun pq : p ∨ q => show False from Or.elim pq
      (fun hp => show False from hnpnq.left hp)
      (fun hq => show False from hnpnq.right hq))


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
example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun hnpnq : ¬p ∨ ¬q =>
    fun hpq : p ∧ q => show False from Or.elim hnpnq
    (fun hnp => show False from hnp hpq.left)
    (fun hnq => show False from hnq hpq.right)


--------------------------------------------------------------------------------------------------------
/-
¬(p ∧ ¬p)

1  |_ p ∧ ¬p
2  |  p                And.left 1
3  |  ¬p               And.right 1
4  |  False            Apply 3,2
5  (p ∧ ¬p) → False    Conditional proof 1-4
6  ¬(p ∧ ¬p)           ¬ Definition 5
-/
example : ¬(p ∧ ¬p) :=
  fun hpnp : p ∧ ¬p =>
    show False from hpnp.right hpnp.left

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
example : p ∧ ¬q → ¬(p → q) :=
  fun hpnpq : p ∧ ¬q =>
    fun hpq : p → q => show False from hpnpq.right (hpq hpnpq.left)

example : p ∧ ¬q → ¬(p → q) :=
  fun hpnpq : p ∧ ¬q =>
  -- False.elim allows to deduce 'False' from 'False', which is unnecessary.
    fun hpq : p → q => show False from False.elim ((hpnpq.right : ¬q) ((hpq hpnpq.left) : q))

----------------------------------------------------------------------------------------------
/-
¬p → (p → q)

1  |_ ¬p
2  |  |_ p
3  |  |  False              Apply 1,2
4  |  |  q                  False.elim 3 (Ex falso quodlibet, 'q' deduced from False.)
5  |  p → q                 Conditional proof: 2-4
6  ¬p → (p → q)             Conditional proof: 1-5
-/
example : ¬p → (p → q) :=
  fun hnp : ¬p =>
    fun hp : p => show q from False.elim (hnp hp)

-- Using 'absurd'.
example : ¬p → (p → q) :=
  fun hnp : ¬p =>
    fun hp : p => show q from absurd hp hnp


---------------------------------------------------------------------------------------------
-- Example: How to prove that 42 = 7 from False?
/-
False → 42 = 7 means: "If False is true, then 42 = 7."

1  |_ False
2  |  42 = 7              False.elim 1
3  False → 42 = 7         Conditional proof: 1-2
-/
example : False → 42 = 7 := by
  intro (h : False)
  exact (False.elim h : 42 = 7)


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
example : (¬p ∨ q) → (p → q) :=
  fun hnpq : ¬p ∨ q =>
    fun hp : p => Or.elim hnpq
    (fun hnp => show q from False.elim (hnp hp))
    (fun hq => show q from hq)

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
example : p ∨ False ↔ p :=
  Iff.intro
  (fun hpf : p ∨ False =>
    Or.elim hpf
    (fun hp => hp)
    (fun hf => False.elim hf))
  (fun hp => Or.inl hp)

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
example : p ∧ False ↔ False :=
  Iff.intro
  (fun hpf => hpf.right)
  (fun hf => And.intro (False.elim hf) hf)

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
example : (p → q) → (¬q → ¬p) :=
  fun hpq => fun hnq => fun hp => hnq (hpq hp)




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
example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  fun hpqr =>
    Or.elim (em p)
      (fun hp => Or.elim (hpqr hp)
        (fun hq => Or.inl fun _ => hq)
        (fun hr => Or.inr fun _ => hr))
      (fun hnp => Or.inl fun hp => False.elim (hnp hp))

-- byCases is equivalent to em.
example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  fun hpqr =>
    byCases
      (fun hp => Or.elim (hpqr hp)
        (fun hq => Or.inl fun _ => hq)
        (fun hr => Or.inr fun _ => hr))
      (fun hnp => Or.inl fun hp => False.elim (hnp hp))

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
example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  fun hpqr =>
    Or.elim (em (p → q))
      (fun hpq : p → q => Or.inl hpq)
      (fun hnpq : ¬(p → q) =>
        Or.inr (fun hp =>
           Or.elim (hpqr hp)
           (fun hq => False.elim (hnpq (fun _ => hq)))
           (fun hr => hr)))

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  fun hpqr =>
    match Classical.em (p → q) with
    | Or.inl hpq => Or.inl hpq
    | Or.inr hnpq =>
        Or.inr (fun hp =>
          match hpqr hp with
          | Or.inl hq =>
              False.elim (hnpq (fun _ => hq))
          | Or.inr hr => hr)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  fun hpqr =>
    byCases
      (fun hpq : p → q => Or.inl hpq)
      (fun hnpq : ¬(p → q) =>
        Or.inr (fun hp =>
          match hpqr hp with          -- Equivalent to Or.elim
          | Or.inl hq => False.elim (hnpq (fun _ => hq))
          | Or.inr hr => hr))

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
example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  fun hnpq =>
    Or.elim (em p)
      (fun hp => Or.inr fun hq => hnpq (And.intro hp hq))
      (fun hnp => Or.inl hnp)

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  fun hnpq =>
    byCases
      (fun hp : p =>
        byCases
          (fun hq : q => False.elim (hnpq ⟨hp, hq⟩))
          (fun hnq => Or.inr hnq))
      (fun hnp => Or.inl hnp)

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  fun hnpq =>
    byCases
    (fun hp : p => Or.inr (fun hq => hnpq ⟨hp, hq⟩))
    (fun hnp => Or.inl hnp)

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
example (p q : Prop) : ¬(p ∧ ¬q) → (p → q) :=
 (fun hnpnq : ¬(p ∧ ¬q) =>
  fun hp : p =>
    Or.elim (em q)
      (fun hq => hq)
      (fun hnq => False.elim (hnpnq ⟨hp, hnq⟩)))

example (p q : Prop) : ¬(p ∧ ¬q) → (p → q) :=
 (fun hnpnq : ¬(p ∧ ¬q) =>
  fun hp : p =>
    Or.elim (em q)
      (fun hq => hq)
      (fun hnq => absurd ⟨hp, hnq⟩ hnpnq ))

------------------------------------------------------------------------------------------------
/-
¬(p → q) → p ∧ ¬q

1  |_ ¬(p → q)
2  |  p ∨ ¬p                  Excluded middle p
3  |  |_ p
4  |  |  |_ q
5  |  |  |  |_ p
6  |  |  |  |  q              Reiteration 5
7  |  |  |  p → q             Conditional proof 5-6
8  |  |  |  False             Apply 1,7
9  |  |  q → False            Conditional proof 4-8
10 |  |  ¬q                   ¬ Definition 9
11 |  |  p ∧ ¬q               And.intro 3,9

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
example : ¬(p → q) → p ∧ ¬q :=
 fun hnpq =>
    Or.elim (em p)
      (fun hp => And.intro hp (fun hq => hnpq (fun _ => hq)))
      (fun hnp => False.elim (hnpq ((fun hp => False.elim (hnp hp) : p → q))))

example : ¬(p → q) → p ∧ ¬q :=
 fun hnpq =>
    Or.elim (em p)
      (fun hp => And.intro hp (fun hq => hnpq (fun _ => hq)))
      (fun hnp => absurd (fun hp => absurd hp hnp) hnpq)

-- ByContradiction is equivalent to excluded middle or to double negation elimination.
/-

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
example : ¬(p → q) → p ∧ ¬q :=
  fun hnpq =>
    let hp : p :=
      byContradiction fun hnp => -- ByContradiction is equivalent to excluded middle or double negation elimination, see example below.
        hnpq (fun hp => absurd hp hnp)

    let hnq : ¬q :=
      fun hq => hnpq (fun _ => hq)

    ⟨hp, hnq⟩

example : ¬(p → q) → p ∧ ¬q :=
  fun hnpq =>
    let hp : p :=
      Or.elim (Classical.em p)
        (fun hp => hp)
        (fun hnp => False.elim (hnpq (fun hp => absurd hp hnp)))

    let hnq : ¬q :=
      fun hq => hnpq (fun _ => hq)

    ⟨hp, hnq⟩

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
example : (p → q) → (¬p ∨ q) :=
 fun hpq =>
    Or.elim (em p)
      (fun hp => Or.inr (hpq hp))
      (fun hnp => Or.inl hnp)

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
example : (p → q) → (¬p ∨ q) :=
 fun hpq =>
    Or.elim (em p)
      (fun hp => Or.inr (show q from byContradiction (fun hnq => hnq (hpq hp))))
      (fun hnp => Or.inl hnp)

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
example : (¬q → ¬p) → (p → q) :=
  fun hnqnp =>
    fun hp : p =>
      Or.elim (em q)
        (fun hq => hq)
        (fun hnq => absurd hp (hnqnp hnq))

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
example : (¬q → ¬p) → (p → q) :=
 fun hnqnp =>
  fun hp : p =>
    Or.elim (em p)
      (fun hp => show q from byContradiction ((fun hnq => (hnqnp hnq : ¬ p) hp) : (¬¬q))) -- (¬¬ q) = (¬p → False)
      (fun hnp => False.elim (hnp hp))

-----------------------------------------------------------------------------------------------------------
/-
p ∨ ¬p

1 p ∨ ¬p  Excluded Middle (em p)
-/
example : p ∨ ¬p := em p

example : p ∨ ¬p :=
  byCases (fun hp => Or.inl hp) (fun hnp => Or.inr hnp)

example : p ∨ ¬p :=
  Or.elim (em p)
    (fun hp => Or.inl hp)
    (fun hnp => Or.inr hnp)

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
example : (((p → q) → p) → p) :=
  fun hpqp =>
    Or.elim (em p)
      (fun hp => hp)
      (fun hnp =>
        hpqp (fun hp => False.elim (hnp hp)))

example : (((p → q) → p) → p) :=
fun hpqp =>
  Or.elim (em p)
    (fun hp => hp)
    (fun hnp =>
        let hp : p := by
          apply hpqp
          intro hp
          contradiction
        hp)


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
example : (((p → q) → p) → p) :=
  Or.elim (em p)
    (fun hp => fun _ => hp)
    (fun hnp =>
      fun hpqp =>
        hpqp (fun hp => False.elim (hnp hp)))

example : (((p → q) → p) → p) :=
  Or.elim (em p)
    (fun hp => fun hpqp => hp)
    (fun hnp =>
      fun hpqp =>
        let hp : p := by
          apply hpqp
          intro hp
          contradiction
        hp)


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
-- Using 'have' to avoid having to calculate twice p → False.
example : ¬(p ↔ ¬p) :=
  fun h : p ↔ ¬p =>
    have hpFalse : p → False := fun hp : p => (h.mp hp : ¬ p) hp
    hpFalse (h.mpr hpFalse)

-- 'let' and 'have' are interchangeable here.
example : ¬(p ↔ ¬p) :=
  fun h =>
    let hpq : p → ¬p := Iff.mp h
    let hqp : ¬p → p := Iff.mpr h
    have hnpFalse : p → False := fun hp => hpq hp hp
    have hp : p := hqp hnpFalse
    show False from hnpFalse hp

/-
Without using 'have', we need to duplicate the proof of p → False, which is unnecessary in the natural deduction diagram.
In the diagram, each line is numbered, allowing us to refer to it, similar to how 'have' is used in Lean.

¬(p ↔ ¬p)

1  |_ p ↔ ¬p
2  |  |_ p
3  |  |  p → ¬p         Iff.mp 1
4  |  |  ¬p             Apply 2,3
5  |  |  False          Apply 3,2
6  |  p → False         Conditional proof 2-5
7  |  |_ p
8  |  |  p → ¬p         Iff.mp 1
9  |  |  ¬p             Apply 8,7
11 |  |  False          Apply 9,7
12 |  p → False         Conditional proof 7-11
13 |  ¬p → p            Iff.mpr 1
14 |  p                 Apply 13,12   (using 12, which is the second p → False)
15 |  False             Apply 6,14    (using 6, which is the first p → False)
16  (p ↔ ¬p) → False    Conditional proof 1-15
17  ¬(p ↔ ¬p)           ¬ Definition 16
-/
example : ¬(p ↔ ¬p) :=
  fun h : p ↔ ¬p =>
    False.elim (
      (fun hp => (h.mp hp : ¬ p) hp)
      (h.mpr (fun hp => (h.mp hp : ¬ p) hp)))
