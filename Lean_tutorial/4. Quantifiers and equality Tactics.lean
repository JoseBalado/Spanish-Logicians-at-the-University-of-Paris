-----------------------------------------------------------------------------------------------------------------------
-- # Deduction rules and definitions:
-- Defintion of ¬.  In Lean, ¬ p is defined as p → False.

-- byContradiction is equivalent to Double Negation Elimination.

-- ByContradiction can reduce ¬¬ p to p, and what is equivalent ¬ p → False to p.

-- Use `cases` to destructure Existential Quantifiers and disjunctions.

-- With 'have', and in general, Favor using '¬¬' instead of '→ False' like:
--  have hnnexpx     : ¬¬ ∃ x, p x        := by
--  have hnexpxFalse : ¬ ∃ x, p x → False := by


-- # General notes for natural deduction diagrams
-- In the natural deduction diagrams we use the following naming conventions:
---- 'w' short for 'witness', is the witness that comes from Exists.elim. Used by Exists.elim and Exists.intro.
---- 'a' short for 'any', represents an arbitrary element used by ∀-intro (fun a).

/- ## How to represent theorems given before the ⊢ symbol in natural deduction diagrams.
L, A ⊢ C → A

L
A
|_ C
|  A
C → A

In lean:
example L A : C →  A
-/

/- ## Difference between direct proof and implication in classical logic
(Copilot)
There is a subtle difference in how the two statements are interpreted in terms of truth values:

1. ¬ ∀ x, ¬ p x ⊢ ∃ x, p x
This is a direct proof. It asserts that ¬ ∀ x, ¬ p x is true, and from this truth, ∃ x, p x is derived.
Since ¬ ∀ x, ¬ p x is assumed to be true (as it is a theorem), ∃ x, p x must also be true.

Key Point: The truth of ¬ ∀ x, ¬ p x guarantees the truth of ∃ x, p x.

2. ¬ ∀ x, ¬ p x → ∃ x, p x
This is an implication. It states that if ¬ ∀ x, ¬ p x is true, then ∃ x, p x must also be true.

However, in classical logic, an implication A → B is true even if A is false. This is because an implication is only false when A is true and B is false.
Key Point: If ¬ ∀ x, ¬ p x is false, the implication ¬ ∀ x, ¬ p x → ∃ x, p x can still be true, regardless of the truth value of ∃ x, p x.

Summary of Differences:
Direct Proof (⊢): Assumes ¬ ∀ x, ¬ p x is true and derives ∃ x, p x. Both must be true.
Implication (→): Does not assume ¬ ∀ x, ¬ p x is true. The implication can be true even if ¬ ∀ x, ¬ p x is false.
In classical logic, the implication ¬ ∀ x, ¬ p x → ∃ x, p x is broader in scope because it does not require ¬ ∀ x, ¬ p x to be true for the statement itself to hold.
-/


-- # Book examples
-- ## 4.1. The Universal Quantifier
/- (ChatGPT)
1. intro (h : ∀ x : α, p x ∧ q x) =>
  You're given a function h that takes any x in α and returns a proof of p x ∧ q x.

2. intro (a : α) =>
  You're defining a function that takes an arbitrary element 'a' of α.
  At this point, 'a' is a bound variable — it could be anything.

3. h a
  You're now applying h to a specific 'a'. At this point, you're treating 'a' as an individual:
  You’re saying: “For this particular 'a', I want to extract the proof of 'p a'.”

4. And.left hpaqa
  'h a' gives a proof of 'p a ∧ q a'.
  And.left extracts the proof of 'p a' from that conjunction.
-/
/-
(α : Type) (p q : α → Prop)
(∀ x : α, p x ∧ q x) → ∀ y : α, p y

1  |_ ∀ x, p x ∧ q x
2  |  |_ a
3  |  |  p a ∧ q a                Apply 1,2
4  |  |  p a                      And.left 3
5  |  ∀ y : α, p y                ∀ intro 2-4
6  (∀ x, p x ∧ q x) → ∀ y, p y    Conditional proof 1-5
-/
example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y := by
  intro (h : ∀ x : α, p x ∧ q x)
  . intro (a : α)
    have hpaqa : p a ∧ q a := h a
    exact (And.left hpaqa : p a)


/-
Lean automatically lifts α to a universe-polymorphic type parameter. This is why you don’t need to write (α : Type) explicitly.
Lean figures it out because α appears as the domain of p and q.

(p q : α → Prop) (∀ x : α, p x ∧ q x) → ∀ x : α, p x

1  |_ ∀ x, p x ∧ q x
2  |  |_ a
3  |  |  p a ∧ q a                Apply 1,2
4  |  |  p a                      And.left 3
5  |  ∀ y, p y                    ∀ intro 2-4
6  (∀ x, p x ∧ q x) → ∀ x, p x    Conditional proof 1-5
-/
example (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y := by
  intro (h : ∀ x : α, p x ∧ q x)
  . intro (a : α)
    have hpaqa : p a ∧ q a := h a
    exact (And.left hpaqa : p a)


-- ## 4.4. The Existential Quantifier
-- Many of the exercises from now on depend on p and q being propositions.
-- So we declare them as variables of type α → Prop.
-- Lean automatically infers 'α' as the type of the variables 'p' and 'q',
-- We declare 'α' implicitly here, but there is no need to do so.
variable {α} (p q : α → Prop)

-----------------------------------------------------------------------------------------------------------------------------
-- https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html#the-existential-quantifier
-- My example, to make it as similar as possible as the universal quantifier example.

/-
(α : Type) (p q : α → Prop) : (h : ∃ x, p x ∧ q x) → ∃ x, p x

1  |_ ∃ x, p x ∧ q x
2  |  |_ w
3  |  |  |_ p w ∧ q w
4  |  |  |  p w                   And.left 3
5  |  |  |  ∃ x, p x              Exists.intro 2,4
6  |  |  ∃ x, p x                 Exists.elim proof 3-5    Note 1.
7  |  ∃ x, p x                    Exists.elim witness 2-6  Note 2.
8  (∃ x, p x ∧ q x) → ∃ x, p x    Conditional Proof 1-7

Note 1: Exists.elim proof shows what we were able to prove assuming 'p w ∧ q w', and repeats the previous line ending the assumption.
Note 2: Exists.elim witness comes immediately after Exists.elim proof repeating what Exists.elim proof showed and ending the assumption.

------------------
Natural deduction
|_ w
|  |_ p w ∧ q w

Represents tactics
intro w
hpq
-/
example : (h : ∃ x, p x ∧ q x) → ∃ x, p x := by
  intro (h : ∃ x, p x ∧ q x)
  cases h with
  | intro w hpwqw =>
    have hpw : p w := And.left hpwqw
    exact (Exists.intro w hpw : ∃ x, p x)

-- Example using 'match'.
example (p q : α → Prop) : (h : ∃ x, p x ∧ q x) → ∃ x, p x := by
  intro (h : ∃ x, p x ∧ q x)
  match h with
  | ⟨w, hpwqw⟩ => exact ⟨w, And.left hpwqw⟩

/- (ChatGPT))
1. '| intro w hpq =>'
This is a pattern-matching branch for the constructor Exists.intro.

intro here does not mean the tactic intro.
Instead, it refers to the constructor Exists.intro, which builds witnesses of ∃ x, p x ∧ q x.

where:
  'w : α' is the witness,
  hpq : p w ∧ q w is the proof that w satisfies the property.

2. w
  This binds the witness of type α from the existential.

3. hpq
  This binds the proof term of type p w ∧ q w.

4. 'And.right hpq' is the proof that 'q' holds for 'w'.

5. 'And.left hpq' is the proof that 'p' holds for 'w'.

6. 'Exists.intro w hqp'
  Exists.intro is the constructor of the existential quantifier.
  This is constructing a new existential proof: ∃ x, q x ∧ p x

So it takes:
  a witness w : α,
  a proof of the property for that witness, here q w ∧ p w,
  and returns ∃ x, q x ∧ p x.

  We apply the constructor (Exists.intro) to combine the witness 'w' and its property 'hqp' into an existential proof.
-/

/-
(h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x

1  ∃ x, p x ∧ q x
2  |_ w
3  |  |_ p w ∧ q w
4  |  |  q w              And.right 3
5  |  |  p w              And.left 3
6  |  |  q w ∧ p w        And.intro 4,5
7  |  |  ∃ x, q x ∧ p x   Exists.intro 2,6
8  |  ∃ x, q x ∧ p x      Exists.elim proof  3-7 (p w ∧ q w → ∃ x, q x ∧ p x)
9  ∃ x, q x ∧ p x         Exists.elim witness 2-8  (∀ (w : α), p w ∧ q w → ∃ x, q x ∧ p x)
-/
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x := by
  cases h with
  | intro w hpq =>
    have hqw : q w := And.right hpq
    have hpw : p w := And.left hpq
    have hqwpw : q w ∧ p w := And.intro hqw hpw
    exact Exists.intro w hqwpw

example (α : Type) (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro (h : ∃ x, p x ∧ q x)
  match h with
  | ⟨w, hpwqw⟩ =>
    have hqw : q w := And.right hpwqw
    have hpw : p w := And.left hpwqw
    have hqwpw : q w ∧ p w := And.intro hqw hpw
    exact Exists.intro w hqwpw


-----------------------------------------------------------------------------------------------------
/-
(∃ x : α, r) → r

1  |_ ∃ x : α, r
2  |  |_ w
3  |  |  |_ r
4  |  |  |  r          Reiteration 3
5  |  |  r             Exists.elim proof 2-4
6  |  r                Exists.elim witness 1-3
7  (∃ x : α, r) → r    Conditional proof 1-6
-/
example : (∃ x : α, r) → r := by
  intro (h : ∃ x : α, r)
  cases h with
  | intro w hr =>
    exact hr

example : (∃ _ : α, r) → r := by
  intro (h : ∃ x : α, r)
  match h with
  | ⟨w, hr⟩ =>
    exact hr


------------------------------------------------------------------------------------------------------
/-
(a : α) : r → (∃ x : α, r)

1  a                  Given witness
2  |_ r
3  |  ∃ x : α, r      Exists.intro 1,2
4  (∃ x : α, r) → r   Conditional proof 1-3
-/
example (a : α) : r → (∃ x : α, r) := by
  intro (hr : r)
  exact Exists.intro a hr

example (a : α) : r → (∃ _ : α, r) := by -- A hole (or placeholder term), which stands for an unknown term.
  intro (hr : r)
  exact Exists.intro a hr


------------------------------------------------------------------------------------------------------
/-
(∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r

1  |  ∃ x, p x ∧ r
2  |  |_ w
3  |  |  |_ p w ∧ r
4  |  |  |  p w                       And.left 3
5  |  |  |  r                         And.right 3
6  |  |  |  ∃ x, p x                  Exists.intro 2,4
7  |  |  |  (∃ x, p x) ∧ r            And.intro 6,5
8  |  |  (∃ x, p x) ∧ r               Exists.elim proof 3-7
9  |  (∃ x, p x) ∧ r                  Exists.elim witness 2-8
10 (∃ x, p x ∧ r) → (∃ x, p x) ∧ r    Conditional proof 1-9

11 |_ (∃ x, p x) ∧ r
12 |  ∃ x, p x                        And.left 11
13 |  r                               And.right 11
14 |  |_ w
15 |  |  |_ p w
16 |  |  |  p w ∧ r                   And.intro 15,13
17 |  |  |  ∃ x, p x ∧ r              Exists.intro 14,16
18 |  |  ∃ x, p x ∧ r                 Exists.elim proof 15-17
19 |  ∃ x, p x ∧ r                    Exists.elim witness 14-18
20 (∃ x, p x) ∧ r → (∃ x, p x ∧ r)    Conditional proof 11-19

21 (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r    Iff.intro: 10,20
-/
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  have hmp : (∃ x, p x ∧ r) → (∃ x, p x) ∧ r := by
    intro (h : ∃ x, p x ∧ r)
    cases h with
    | intro w hpwr =>
      have hpw : p w := And.left hpwr
      have hr : r := And.right hpwr
      have hexpx : (∃ x, p x)  :=  Exists.intro w hpw
      exact (And.intro hexpx hr : (∃ x, p x) ∧ r)

  have hmpr : (∃ x, p x) ∧ r → (∃ x, p x ∧ r) := by
    intro (h : (∃ x, p x) ∧ r)
    cases h with
    | intro hexpx hr =>
      have hr : r := hr
      cases hexpx with
      | intro w hpw =>
        have hpwr : p w ∧ r := And.intro hpw hr
        exact (Exists.intro w hpwr : ∃ x, p x ∧ r)
  exact Iff.intro hmp hmpr

-- Using 'apply 'Iff.intro' as first step.
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  apply Iff.intro
  · intro (h : ∃ x, p x ∧ r)
    cases h with
    | intro w hpwr =>
      have hpw : p w := And.left hpwr
      have hr : r := And.right hpwr
      have hexpx : (∃ x, p x)  :=  Exists.intro w hpw
      exact (And.intro hexpx hr : (∃ x, p x) ∧ r)

  · intro (h : (∃ x, p x) ∧ r)
    cases h with
    | intro hexpx hr =>
      have hr : r := hr
      cases hexpx with
      | intro w hpw =>
        have hpwr : p w ∧ r := And.intro hpw hr
        exact (Exists.intro w hpwr : ∃ x, p x ∧ r)

-- Using 'apply' only to 'Iff.intro' and term mode for the rest.
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  apply Iff.intro
    (fun ⟨w, (hpwr : p w ∧ r)⟩ => And.intro (Exists.intro w (And.left hpwr)) (And.right hpwr))
    (fun ⟨⟨w, (hpw : p w)⟩, (hr : r)⟩ => Exists.intro w (And.intro hpw hr))


------------------------------------------------------------------------------------------------------
/-
(∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x)

1  |_ ∃ x, p x ∨ q x
2  |  |_ w
3  |  |  |_ p w ∨ q w
4  |  |  |  |_ p w
5  |  |  |  | (∃ x, p x)                        Exists.intro 2,4
6  |  |  |  | (∃ x, p x) ∨ (∃ x, q x)           Or.inl 5

7  |  |  |  |_ q w
8  |  |  |  |  ∃ x, q x                         Exists.intro 2,7
9  |  |  |  |  (∃ x, p x) ∨ (∃ x, q x)          Or.inr 8
10 |  |  |  (∃ x, p x) ∨ (∃ x, q x)             Or.elim 3, 4-6, 7-9
11 |  |  (∃ x, p x) ∨ (∃ x, q x)                Exists.elim proof 3-10
12 |  ∃ x, p x ∨ q x                            Exists.elim witness 2-11
13 (∃ x, p x ∨ q x) → (∃ x, p x) ∨ (∃ x, q x)   Conditional proof 1-12

14  |_ (∃ x, p x) ∨ (∃ x, q x)
15  |  |_ ∃ x, p x
16  |  |  |_ w
17  |  |  |  |_ p w
18  |  |  |  |  p w ∨ q w                       Or.inl 17
19  |  |  |  |  ∃ x, p x ∨ q x                  Exists.intro 16,18
20  |  |  |  ∃ x, p x ∨ q x                     Exists.elim proof 17-19
21  |  |  ∃ x, p x ∨ q x                        Exists.elim witness 16-20

22  |  |_ ∃ x, q x
23  |  |  |_ w
24  |  |  |  |_ q w
25  |  |  |  |  p w ∨ q w                        Or.inr 24
26  |  |  |  |  ∃ x, p x ∨ q x                   Exists.intro 23,25
27  |  |  |  ∃ x, p x ∨ q x                      Exists.elim proof 24-26
28  |  |  ∃ x, p x ∨ q x                         Exists.elim witness 23-27
29  |  ∃ x, p x ∨ q x                            Or.elim 14, 15-21, 22-28
30  (∃ x, p x) ∨ (∃ x, q x) → (∃ x, p x ∨ q x)   Conditional proof 14-29

31  (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x)   Iff.intro 13,30
-/
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  apply Iff.intro
  · intro (h : ∃ x, p x ∨ q x)
    cases h with
    | intro w hpwq =>
      cases (hpwq : p w ∨ q w) with
      | inl hpw =>
        have hpx : (∃ x, p x) := Exists.intro w hpw
        exact (Or.inl hpx)
      | inr hqw =>
        have hqx : (∃ x, q x) := Exists.intro w hqw
        exact (Or.inr hqx)

  · intro (h : (∃ x, p x) ∨ (∃ x, q x))
    cases h with
    | inl hexpx =>
      cases hexpx with
      | intro w hpw =>
        have hpwqw : p w ∨ q w := Or.inl hpw
        exact (Exists.intro w hpwqw : ∃ x, p x ∨ q x)
    | inr hexqx =>
      cases hexqx with
      | intro w hqw =>
        have hpwqw : p w ∨ q w := Or.inr hqw
        exact (Exists.intro w hpwqw : ∃ x, p x ∨ q x)


------------------------------------------------------------------------------------------------------
/- (ChatGPT)
1. 'intro a'
Assume 'a : α' for some type 'α'
'a' here is a bound variable — not a specific value yet.
Which is equivalent to: "for any x..."

2. 'intro pa'
Now assume 'pa : p a', i.e., a proof that 'p a' holds for this arbitrary 'a'.

3. 'Exists.intro a pa'
Construct a proof of ∃ x, p x using the witness 'a' and proof 'p a'.

Here, 'a' has changed roles:
In 'intro a', it’s a general variable (used to define a universal statement)
In 'Exists.intro a pa', it becomes an individual — a concrete value you're packaging into an existential ∃ x, p x

| Expression          | What is `a`?         | Role                                             |
| ------------------- | -------------------- | ------------------------------------------------ |
| `intro a`           | Variable (universal) | You’re defining something that works for all `a` |
| `Exists.intro a pa` | Individual (witness) | You use `a` as a witness to construct `∃ x, p x` |


(¬ ∀ x, ¬ p x) : ∃ x, p x

1  ¬ ∀ x, ¬ p x
2  |_ ¬ ∃ x, p x
3  |  |_ a
4  |  |  |_ p a
5  |  |  |  ∃ x, p x            Exists.intro 3,4
6  |  |  |  False               Apply 2,5
7  |  |  p x → False            Conditional proof 4-6 (p x → False)
8  |  |  ¬ p x                  ¬ Definition 7
9  |  ∀ x, ¬ p x                ∀-intro 3-8
10 |  False                     Apply 1,9
11 ¬ ∃ x, p x → False           Conditional proof 2-6
12 ∃ x, p x                     ByContradiction 11 (Double Negation Elimination)
-/
example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x := by
  have hnnexpx : ¬¬ ∃ x, p x := by
    intro (hnexpx : ¬ ∃ x, p x)
    have haxnpx : ∀ x, ¬ p x := by
      intro (a : α)
      . intro (pa : p a)
        have hexpx : ∃ x, p x := Exists.intro a pa
        exact (hnexpx hexpx : False)
      -- No need for another 'exact' here. Tactics automatically deduces '∀ x, ¬ p x' from '¬ p x'.
    exact (h haxnpx : False)
    -- Tactics automatically converts '¬ ∃ x, p x → False' into '¬¬ ∃ x, p x'.
  exact Classical.byContradiction hnnexpx

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x := by
  exact Classical.byContradiction (by
    intro hnexpx
    apply h
    intro a pa
    apply hnexpx
    exact Exists.intro a pa)

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x := by
  cases Classical.em (∃ x, p x) with
  | inl hexpx =>
    exact hexpx
  | inr hnexpx =>
    have hforall : ∀ x, ¬ p x := by
      intro a pa
      exact hnexpx (Exists.intro a pa)
    exact (h hforall).elim


--------------------------------------------------------------------------------------------------------
/-
(∀ x, p x) ↔ ¬ (∃ x, ¬ p x)

1  |_ ∀ x, p x
2  |  |_ ∃ x, ¬ p x
3  |  |  |_ w
4  |  |  |  |_ ¬ p w
5  |  |  |  |  p w               Apply 1,3
6  |  |  |  |  False             Apply 4,5
7  |  |  |  False                Exists.elim proof 4-6
8  |  |  False                   Exists.elim witness 3-7
9  |  (∃ x, ¬ p x) → False       Conditional proof 2-8
10 |  ¬ (∃ x, ¬ p x)             ¬ Definition 9
11 (∀ x, p x) → ¬ (∃ x, ¬ p x)   Conditional proof 1-10

12  |_ ¬ (∃ x, ¬p x)
13  |  |_ a
14  |  |  |_ ¬ p a
15  |  |  |  ∃ x, ¬ p x          Exists.intro 12,13
16  |  |  |  False               Apply 11,14
17  |  |  ¬ p a → False          Conditional proof 13-15
18  |  |  p x                    ByContradiction 17 (Double Negation Elimination)
19  |  ∀ x, p x                  ∀ intro 12-16
20  ¬ (∃ x, ¬ p x) → ∀ x, p x    Conditional proof 11-18

21 (∀ x, p x) ↔ ¬ (∃ x, ¬ p x)   Iff.intro 11,20
-/
example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  have hmp : (∀ x, p x) → ¬ (∃ x, ¬ p x) := by
    intro (hapx : ∀ x, p x)
    . intro (hexnp : ∃ x, ¬ p x)
      cases hexnp with
      | intro w hnpx =>
        have hpw : p w := hapx w
        exact (hnpx hpw : False)

  have hmpr : ¬ (∃ x, ¬ p x) → (∀ x, p x) := by
    · intro (hnexnpx : ¬ ∃ x, ¬ p x)
      . intro (a : α)
        have hnnpa : ¬¬ p a := by
          intro (npa : ¬ p a)
          have hexnp : ∃ x, ¬ p x := Exists.intro a npa
          exact (hnexnpx hexnp : False)
        exact Classical.byContradiction hnnpa
  exact Iff.intro hmp hmpr

-- Example using '→ False' in a 'have'.
example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  have hmp : (∀ x, p x) → ¬ (∃ x, ¬ p x) := by
    intro (hapx : ∀ x, p x)
    . intro (hexnp : ∃ x, ¬ p x)
      cases hexnp with
      | intro w hnpx =>
        have hpw : p w := hapx w
        exact (hnpx hpw : False)

  have hmpr : ¬ (∃ x, ¬ p x) → (∀ x, p x) := by
    · intro (hnexnpx : ¬ ∃ x, ¬ p x)
      . intro (a : α)
        have hnpa : ¬ p a → False := by
          intro (npa : ¬ p a)
          have hexnp : ∃ x, ¬ p x := Exists.intro a npa
          exact (hnexnpx hexnp : False)
        exact Classical.byContradiction hnpa
  exact Iff.intro hmp hmpr


-----------------------------------------------------------------------------------------------------------
/-
(∃ x, p x) ↔ ¬ (∀ x, ¬ p x)

1  |_ ∃ x, p x
2  |  |_ ∀ x, ¬ p x
3  |  |  |_ w
4  |  |  |  |_ p w
5  |  |  |  |  ¬ p w               Apply 2,3
6  |  |  |  |  False               Apply 5,4
7  |  |  |  False                  Exists.elim proof 4-6
8  |  |  False                     Exists.elim witness 3-7
9  |  ∀ x, ¬ p x → False           Conditional proof 2-8
10 |  ¬ (∀ x, ¬ p x)               ¬ Definition 9
11 (∃ x, p x) → ¬ (∀ x, ¬ p x)     Conditional proof 1-10

12  |_ ¬ (∀ x, ¬ p x)
13  |  |_ ¬ ∃ x, p x
14  |  |  |_ a
15  |  |  |  |_ p a
16  |  |  |  |  ∃ x, p x           Exists.intro 14,15
17  |  |  |  |  False              Apply 13,16
18  |  |  |  p a → False           Conditional proof 15-17
19  |  |  |  ¬ p a                 ¬ Definition 18
20  |  |  ∀ x, ¬ p x               ∀ intro 14-19
21  |  |  False                    Apply 12,20
22  |  (¬ ∃ x, p x) → False        Conditional proof 13-21
23  |  ∃ x, p x                    ByContradiction 22
24  ¬ (∀ x ¬ p x) → (∃ x, p x)     Conditional proof 12-23

24 (∃ x, p x) ↔ ¬ (∀ x, ¬ p x)     Iff.intro 11,24
-/
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
  apply Iff.intro
  . intro (hexpx : ∃ x, p x)
    . intro (haxnpx : ∀ x, ¬ p x)
      cases hexpx with
      | intro w hpw =>
        have hnpw : ¬ p w := haxnpx w
        exact (hnpw hpw : False)

  . intro (hnaxnpx : ¬ ∀ x, ¬ p x)
    have hnnexpx : ¬¬ ∃ x, p x := by
      intro (hnexpx : ¬ ∃ x, p x)
      have haxnpx : ∀ x, ¬ p x := by
        intro (a : α)
        . intro (hpa : p a)
          have hexpx : ∃ x, p x := Exists.intro a hpa
          exact (hnexpx hexpx : False)
      exact hnaxnpx haxnpx
    exact Classical.byContradiction hnnexpx

-- Assuming '(¬ ∃ x, p x) → False' and '(∃ x, p x) → False'.
-- Watch out for parentheses in both assumptions.
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
  apply Iff.intro
  . intro (hexpx : ∃ x, p x)
    . intro (haxnpx : ∀ x, ¬ p x)
      cases hexpx with
      | intro w hpw =>
        have hnpw : ¬ p w := haxnpx w
        exact (hnpw hpw : False)

  . intro (hnaxnpx : ¬ ∀ x, ¬ p x)
    have hnexpxFalse : (¬ ∃ x, p x) → False := by  -- '→ False'
      intro (hexpxFalse : (∃ x, p x) → False)      -- '→ False'
      have haxnpx : ∀ x, ¬ p x := by
        intro (a : α)
        . intro (hpa : p a)
          have hexpx : ∃ x, p x := Exists.intro a hpa
          exact (hexpxFalse hexpx : False)
      exact hnaxnpx haxnpx
    exact Classical.byContradiction hnexpxFalse


/-
(∃ x, p x) ↔ ¬ (∀ x, ¬ p x)

1  |_ ∃ x, p x
2  |  |_ w
3  |  |  |_ p w
4  |  |  |  |_ ∀ x, ¬ p x
5  |  |  |  |  ¬ p w               Apply 4,2
6  |  |  |  |  False               Apply 5,3
7  |  |  |  (∀ x, ¬ p x) → False   Conditional proof 2-6
8  |  |  |  ¬ (∀ x, ¬ p x)         ¬ Definition 7
9  |  |  ¬ (∀ x, ¬ p x)            Exists.elim proof 3-8
10 |  ¬ (∀ x, ¬ p x)               Exists.elim witness 2-9
11 (∃ x, p x) → ¬ (∀ x, ¬ p x)     Conditional proof 1-10

12  |_ ¬ (∀ x, ¬ p x)
13  |  |_ ¬ ∃ x, p x
14  |  |  |_ a
15  |  |  |  |_ p a
16  |  |  |  |  ∃ x, p x           Exists.intro 14,15
17  |  |  |  |  False              Apply 13,16
18  |  |  |  p a → False           Conditional proof 15-17
19  |  |  |  ¬ p a                 ¬ Definition 18
20  |  |  ∀ x, ¬ p x               ∀ intro 14-19
21  |  |  False                    Apply 12,20
22  |  ¬ ∃ x, p x → False          Conditional proof 13-21
23  |  ∃ x, p x                    ByContradiction 22
24  ¬ (∀ x ¬ p x) → (∃ x, p x)     Conditional proof 12-23

24 (∃ x, p x) ↔ ¬ (∀ x, ¬ p x)     Iff.intro 11,24
-/
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
  apply Iff.intro
  . intro (hexpx : ∃ x, p x)
    cases hexpx with
    | intro w hpw =>
    . intro (haxnpx : ∀ x, ¬ p x)
      have hnpw : ¬ p w := haxnpx w
      exact (hnpw hpw : False)

  . intro (hnaxnpx : ¬ ∀ x, ¬ p x)
    have hnnexpx : ¬¬ ∃ x, p x := by
      intro (hnexpx : ¬ ∃ x, p x)
      have haxnpx : ∀ x, ¬ p x := by
        intro (a : α)
        . intro (hpa : p a)
          have hexpx : ∃ x, p x := Exists.intro a hpa
          exact (hnexpx hexpx : False)
      exact hnaxnpx haxnpx
    exact Classical.byContradiction hnnexpx


-----------------------------------------------------------------------------------------------------------
/-
(¬ ∃ x, p x) ↔ (∀ x, ¬ p x)

1  |_ ¬ ∃ x, p x
2  |  |_ a
3  |  |  |_ p a
4  |  |  |  ∃ x, p x                Exists.intro 2,3
5  |  |  |  False                   Apply 1,4
6  |  |  p x → False                Conditional proof 3-5
7  |  |  ¬ p x                      ¬ Definition 6
8  |  ∀ x, ¬ p x                    ∀ intro 2-7
9  (¬ ∃ x, p x) → (∀ x, ¬ p x)      Conditional proof 1-8

10 |_ ∀ x, ¬ p x
11 |  |_ ∃ x, p x
12 |  |  |_ w
13 |  |  |  |_ p w
14 |  |  |  |  ¬ p w                Apply 10,12
15 |  |  |  |  False                Apply 14,13
16 |  |  |  False                   Exists.elim proof 13-15
17 |  |  False                      Exists.elim witness 12-16
18 |  ∃ x, p x → False              Conditional proof 10-16
19 |  ¬ ∃ x, p x                    ¬ Definition 18
20 (∀ x, ¬ p x) → (¬ ∃ x, p x)      Conditional proof 10-19

21 (¬ ∃ x, p x) ↔ (∀ x, ¬ p x)      Iff.intro 9,20
-/
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  have hmp : (¬∃ x, p x) → (∀ x, ¬ p x) := by
    intro (hnexpx : ¬ ∃ x, p x)
    . intro (a : α)
      . intro (hpa : p a)
        have hexpx : ∃ x, p x := Exists.intro a hpa
        exact (hnexpx hexpx : False)

  have hpr : (∀ x, ¬ p x) → (¬ ∃ x, p x) := by
    intro (haxnpx : ∀ x, ¬ p x)
    . intro (hexpx : ∃ x, p x)
      cases hexpx with
      | intro w hpw =>
        have hnpw : ¬ p w := haxnpx w
        exact (hnpw hpw : False)
  exact Iff.intro hmp hpr


-----------------------------------------------------------------------------------------------------------
/-
(¬ ∀ x, p x) ↔ (∃ x, ¬ p x)

1  |_ ¬ ∀ x, p x
2  |  |_ ¬ ∃ x, ¬ p x
3  |  |  |_ a
4  |  |  |  |_ ¬ p a
5  |  |  |  |  ∃ x, ¬ p x           Exists.intro 3,4
6  |  |  |  |  False                Apply 2,5
7  |  |  |  ¬ p a → False           Conditional proof 4-6
8  |  |  |  p a                     ByContradiction 7 (Double Negation Elimination)
9  |  |  ∀ x, p x                   ∀ intro 3-8
10 |  |  False                      Apply 1,9
11 |  ¬ ∃ x, ¬ p x → False          Conditional proof 2-10
12 |  ∃ x, ¬ p x                    ByContradiction 11
13 (¬ ∀ x, p x) → (∃ x, ¬ p x)      Conditional proof 1-12

14 |_ ∃ x, ¬ p x
15 |  |_ ∀ x, p x
16 |  |  |_ w
17 |  |  |  |_ ¬ p w
18 |  |  |  |  p w                  Apply 15,16
19 |  |  |  |  False                Apply 17,18
20 |  |  |  False                   Exists.elim proof 17-19
21 |  |  False                      Exists.elim witness 16-20
22 |  ∀ x, p x → False              Conditional proof 15-21
23 |  ¬ ∀ x, p x                    ¬ Definition 22
24 (∃ x, ¬ p x) → (¬ ∀ x, p x)      Conditional proof 14-23

25 (¬ ∀ x, p x) ↔ (∃ x, ¬ p x)      Iff introduction: 13,24
-/
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
  apply Iff.intro
  . intro (hnaxpx : ¬ ∀ x, p x)
    have hnnexnpx : ¬¬ ∃ x, ¬ p x := by
      intro (hnexnpx : ¬ ∃ x, ¬ p x)
      have haxpx : ∀ x, p x := by
        intro (a : α)
        have hnnpa : ¬¬ p a := by
          intro (hnpa : ¬ p a)
          have hexnpx : ∃ x, ¬ p x := Exists.intro a hnpa
          exact (hnexnpx hexnpx : False)
        exact Classical.byContradiction hnnpa
      exact hnaxpx haxpx
    exact Classical.byContradiction hnnexnpx

  intro (hexnpx : ∃ x, ¬ p x)
  . intro (haxpx : ∀ x, p x)
    cases hexnpx with
    | intro w hnw =>
      have hpw : p w := haxpx w
      exact (hnw hpw : False)


--------------------------------------------------------------------------------------------------------
/-
(∀ x, p x → r) ↔ (∃ x, p x) → r

1  |_ (∀ x, p x → r)
2  |  |_ ∃ x, p x
3  |  |  |_ w
4  |  |  |  |_ p w
5  |  |  |  |  p w → r   Apply 1,3
6  |  |  |  |  r         Apply 5,4
7  |  |  |  r            Exist.elim proof 4-6
8  |  |  r               Exist.elim witness 3-7
9  |  (∃ x, p x) → r     Conditional Proof 2-8

10 |_ (∃ x, p x) → r
11 |  |_ a
12 |  |  |_ p a
13 |  |  |  ∃ x, p x     Exists.intro 11,12
14 |  |  |  r            Apply 13,10
15 |  |  p a → r         Conditional Proof 12-14
16 |  (∀ x, p x → r)     ∀ intro 11-15

17 (∀ x, p x → r) ↔ (∃ x, p x) → r   Iff.intro 9,17
-/
example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
  apply Iff.intro
  . intro (haxpxpr : ∀ x, p x → r)
    . intro (hexpx : ∃ x, p x)
      cases hexpx with
      | intro w hpw =>
        have hpwr : p w → r := haxpxpr w
        exact (hpwr hpw : r)

  . intro (hexpxr : (∃ x, p x) → r)
    . intro (a : α)
      . intro (hpa : p a)
        have hexpx : ∃ x, p x := Exists.intro a hpa
        exact (hexpxr hexpx : r)


----------------------------------------------------------------------------------------------------------------------------------------------------------
/-
(a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r
(ChatGPT)
This is a logical equivalence between two statements:

1) Left side: (∃ x, p x → r)
  There exists an element x such that if p x holds, then r holds.
  Or: There exists at least one x for which p x implies r.
  Or: There exists an x such that (if p x is true, then r is true).

  If there exists some x such that p x → r, and we know p x holds for every x, then in particular, p x must hold for this specific x. So r follows from p x → r.

2) Right side: (∀ x, p x) → r
  If p x holds for every x, then r holds.

  If (∀ x, p x) → r, then we can define:
  “Pick any x, and note that if p x holds, then r must hold (because ∀ x, p x would be true, and so r would follow)”.
  So for any x, p x → r holds — hence there exists at least one such x.

Note: This equivalence generally requires classical reasoning, because constructively, from (∀ x, p x) → r, we can't necessarily extract a specific x to witness the existential (∃ x, p x → r).


(Copilot)
Example
Suppose p x means "x is a student" and r means "the class is successful":

The left side (∃ x, p x → r) means "there exists an x such that if x is a student, then the class is successful."
The right side (∀ x, p x) → r means "if everyone is a student, then the class is successful." The equivalence shows that these two statements are logically the same.


- ((∀ x, p x) → r) → (∃ x, p x → r)
The variable 'a' is needed to provide a concrete witness for the existential quantifier ∃ x, p x → r in the case where ∀ x, p x holds.
It is introduced outside the proof to simplify the construction and ensure that the proof can refer to a specific element of type α without needing to pick one explicitly within the proof.

For an implication A → B, the conclusion B must follow regardless of whether the antecedent A is true or false:

If A is true, the implication directly guarantees B.
If A is false, the implication is vacuously true (since A → B holds whenever A is false).
In this proof, byCases ensures that both possibilities for ∀ x, p x are addressed, allowing the proof to construct ∃ x, p x → r in either case.

1. ∀ x, p x is true
Then we can simply apply (∀ x, p x) → r to ∀ x, p x and produce a value of type r.
To obtain ∃ x, p x → r, we use the arbitrary 'a : α' that we are given as a witness in the context and construct the function p a → r:
  ⟨a, λ _ => r⟩

This says:
Choose an element 'a : α'.
Then build a function of type p a → r by simply ignoring the input and returning r.
This lets us construct the pair ⟨a, λ _ => r⟩, which has type ∃ x, p x → r.

Here 'a' is just any element of the type α. It doesn't have to satisfy anything special. It's a placeholder used to satisfy the existential.

2. ¬ ∀ x, p x
This is trickier.

We must still produce an ∃ x, p x → r, but we can't construct it directly, because we don't know that p x holds for any x.
So, we argue indirectly by contradiction:
Suppose the conclusion is false:
¬ ∃ x, p x → r

Now, if we can derive a contradiction, then the assumption (¬ ∃ x, p x → r) must be false, and so (∃ x, p x → r) is true.
That’s why we need the second branch: when we can't construct the witness directly, we fall back to indirect reasoning.

Summary
byCases is needed because (∀ x, p x) → r is an implication, and the proof must ensure that the conclusion (∃ x, p x → r) follows regardless of whether the antecedent (∀ x, p x) is true or false.
This is a standard approach in classical logic to handle implications comprehensively.

(Copilot)
Step-by-Step Explanation of ¬ ∀ x, p x:
1. Assume: ¬ ∀ x, p x
fun hnaxpx
This means there exists some x such that ¬ p x.

2. Assume: ¬ ∃ x, p x → r
fun hnexpxr
This means no x satisfies p x → r.

3. Assume an arbitrary (b : α):
fun b
To prove ∀ x, p x, introduce an arbitrary b using fun b.

4. Assume: ¬ p b
fun hnpb

Under this assumption, construct a proof of ∃ x, p x → r:
Assume: p b

From p b, derive 'False':
(¬ p b)(p b)

From 'False', derive r:
False.elim (¬ p b)(p b)
This shows that if p b holds, it leads to a contradiction 'False', from which r follows.

Use 'b' as the witness to derive ∃ x, p x → r:
(Exists.intro b (fun hpb : p b => False.elim (hnpb hpb)

Contradiction:
The proof of ∃ x, p x → r contradicts the assumption ¬ ∃ x, p x → r.
Therefore, ¬ p b cannot hold, and p b must hold for every x.
Conclude ∀ x, p x:

Since p x holds for every x, haxpx : ∀ x, p x is established.
This contradicts the original assumption hnaxpx : ¬ ∀ x, p x.


(a : α)
(∃ x, p x → r) ↔ (∀ x, p x) → r

1  a
2  |_ ∃ x, p x → r
4  |  |_ w
4  |  |  |_ p w → r
5  |  |  |  |_ ∀ x, p x
6  |  |  |  |  p w                   Apply 5,3
7  |  |  |  |  r                     Apply 4,6
8  |  |  |  ∀ x, p x → r             Conditional proof 5-7
9  |  |  ∀ x, p x → r                Exists.elim proof 4-8
10 |  ∀ x, p x → r                   Exists.elim witness 3-9
11 (∃ x, p x → r) → ∀ x, p x → r     Conditional proof 2-10

12 |_ (∀ x, p x) → r
13 |  (∀ x, p x) ∨ (¬ ∀ x, p x)       Excluded middle (em ∀ x, p x)
14 |  |_ ∀ x, p x
15 |  |  |_ p a                       Supposing 'a' has property p, 'a' is taken from the context (a : α).
16 |  |  |  r                         Apply 12,14
17 |  |  p a → r                      Conditional proof 15-16
18 |  |  ∃ x, p x → r                 Exists.intro a,17. Using witness 'a' from the context (a : α).

19 |  |_ ¬ ∀ x, p x
20 |  |  |_ ¬ ∃ x, p x → r
21 |  |  |  |_ b                      Arbitrary b (fun b =>) For ∀ intro.
22 |  |  |  |  |_ ¬ p b               Supposing b doesn't have property p.
23 |  |  |  |  |  |_ p b              Supposing b has property p.
24 |  |  |  |  |  |  False            Apply 22,23
25 |  |  |  |  |  |  r                False.elim 24
26 |  |  |  |  |  p b → r             Conditional Proof 23-25
27 |  |  |  |  |  ∃ x, p x → r        Exists.intro 21,26
28 |  |  |  |  |  False               Apply 20,27
29 |  |  |  |  ¬ p b → False          Conditional proof 22-28
30 |  |  |  |  p b                    byContradiction 29 (Double Negation Elimination)
31 |  |  |  ∀ x, p x                  ∀ intro 21-30
32 |  |  |  False                     Apply 19,31
33 |  |  (¬ ∃ x, p x → r) → False     Conditional proof 20-32
34 |  |  ∃ x, p x → r                 ByContradiction 33
35 |  ∃ x, p x → r                    Or.elim 12, 13-18, 19-34

35 (∃ x, p x → r) ⇔ (∀ x, p x) → r    Iff.intro 11,35
-/
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
  apply Iff.intro
  . intro (hexpxr : ∃ x, p x → r)
    cases hexpxr with
    | intro w hpwr =>
    . intro (haxpx : ∀ x, p x)
      have hpw : p w := haxpx w
      exact (hpwr hpw : r)

  . intro (haxpxr : (∀ x, p x) → r)
    cases Classical.em (∀ x, p x) with
      | inl haxpx =>
        have hpwr : p a → r := by
          intro (hpa : p a)
          exact (haxpxr haxpx : r)
        exact Exists.intro a hpwr

      | inr hnaxpx =>
        have hnexpxrFalse : (¬ ∃ x, p x → r) → False := by
          intro (hnexpxr : ¬ ∃ x, p x → r)
          have haxpx : ∀ x, p x := by
            intro (b : α)
            have hnpbFalse : ¬ p b → False := by
              intro (hnpb : ¬ p b)
              have hexpxr : ∃ x, p x → r := by
                have hpbr : p b → r := by
                  intro (hpb : p b)
                  have hFalse : False := False.elim (hnpb hpb)
                  exact (False.elim hFalse : r)
                exact Exists.intro b hpbr
              exact (hnexpxr hexpxr : False)
            exact Classical.byContradiction hnpbFalse
          exact hnaxpx haxpx
        exact Classical.byContradiction hnexpxrFalse


/-
(a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x)

1  a                                 Given witness 'a' of type α
2  |_ ∃ x, r → p x
3  |  |_ w
4  |  |  |_ r → p w
5  |  |  |  |_ r
6  |  |  |  |  p w                    Apply 4,5
7  |  |  |  |  ∃ x, p x               Exist.intro 3,6
8  |  |  |  r → ∃ x, p x              Conditional Proof 5-7
9  |  |  r → ∃ x, p x                 Exist.elim proof 4-8
10 |  r → ∃ x, p x                    Exist.elim witness 3-9
11 (∃ x, r → p x) → (r → ∃ x, p x)    Conditional proof 2-10

12 |_ r → ∃ x, p x
13 |  r ∨ ¬r                          Excluded Middle (em r)
14 |  |_ r
15 |  |  ∃ x, p x                     Apply 12,14
16 |  |  |_ w
17 |  |  |  |_ p w
18 |  |  |  |  |_ r
19 |  |  |  |  |  p w                 Reiteration 17
20 |  |  |  |  r → p w                Conditional Proof 18-19
21 |  |  |  |  ∃ x, r → p w           Exist.intro 16,20
21 |  |  |  ∃ x, r → p w              Exist.elim Proof 17-20
22 |  |  ∃ x, r → p w                 Exist.elim witness 16-19

23 |  |_ ¬r
24 |  |  |_ r                         (Any variable name will work, but 'r' is used for clarity)
25 |  |  |  False                     Apply 23,24
26 |  |  |  p a                       False.elim 25 ('a' has to be the witness from the context)
27 |  |  r → p a                      Conditional Proof 24-26
28 |  |  ∃ x, r → p x                 Exist.intro 1,27 ('a' has to be the witness from the context)
29 |  ∃ x, x → p x                    Or.elim 13, 14-22, 23-28
30 (r → ∃ x, p x) → (∃ x, r → p x)    Conditional proof 12-29

31 (∃ x, r → p x) ↔ (r → ∃ x, p x)    Iff.intro 11,30
-/
example (a : α) (r : Prop) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
  apply Iff.intro
  . intro (hexrpx : ∃ x, r → p x)
    cases hexrpx with
    | intro w hrpw =>
      intro (hr : r)
      have hpw : p w := hrpw hr
      exact Exists.intro w hpw

  . intro (hrnexpx : r → ∃ x, p x)
    cases Classical.em r with
      | inl hr =>
        have hexpx : ∃ x, p x := hrnexpx hr
        cases hexpx with
        | intro w hpw =>
        have hrpw : r → p w := by
          intro (hr : r)
          exact hpw
        exact Exists.intro w hrpw
      | inr hnr =>
        have hrpw : r → p a := by
          intro (hr : r)
          have hFalse : False := hnr hr
          exact (False.elim hFalse : p a)
        exact Exists.intro a hrpw

example (a : α) (r : Prop) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
  apply Iff.intro
  · intro ⟨w, hrpw⟩
    intro hr
    exact ⟨w, hrpw hr⟩

  · intro hrnexpx
    cases Classical.em r with
    | inl hr =>
      cases hrnexpx hr with
      | intro x px =>
        exact ⟨x, fun _ => px⟩
    | inr hnr =>
      exact ⟨a, fun hr => absurd hr hnr⟩


---------------------------------------------------------------------------------------------------------------------
-- 4.6. Exercises
-- 1. Prove these equivalences:
/-
(∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x)

1  |_ ∀ x, p x ∧ q x
2  |  |_ a                                      Arbitrary a ((intro (a : α)) ∀ intro.
3  |  |  p a ∧ q a                              Apply 1,2
4  |  |  p a                                    And.left 3
6  |  ∀ x, p x                                  ∀ intro 2-4
7  |  |_ a                                      Arbitrary a (fun a =>)
8  |  |  p a ∧ q a                              Apply 1,7
9  |  |  q a                                    And.right 8
10 |  ∀ x, q x                                  ∀ intro 7-9
11 |  (∀ x, p x) ∧ (∀ x, q x)                   And.intro 6,10
12 (∀ x, p x ∧ q x) → (∀ x, p x) ∧ (∀ x, q x)   Conditional Proof 1-11

13 |_ (∀ x, p x) ∧ (∀ x, q x)
14 |  |_ a                                      Arbitrary 'a' for ∀ intro.
15 |  |  ∀ x, p x                               And.left 13
16 |  |  p a                                    Apply 15,14
17 |  |  ∀ x, q x                               And.right 13
18 |  |  q a                                    Apply 17,14
19 |  |  p a ∧ q a                              And.intro 16,18
20 |  ∀ x, p x ∧ q x                            ∀ intro 14-19
21 (∀ x, p x) ∧ (∀ x, q x) → (∀ x, p x ∧ q x)   Conditional Proof 13-20

22 (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x)   Iff.intro 12,21
-/
example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  apply Iff.intro
  . intro (haxpxq : ∀ x, p x ∧ q x)
    have haxpx : ∀ x, p x := by
      intro (a : α)
      have hpaqa : p a ∧ q a := haxpxq a
      exact And.left hpaqa
    have haxqx : ∀ x, q x := by
      intro (a : α)
      have hpaqa : p a ∧ q a := haxpxq a
      exact And.right hpaqa
    exact And.intro haxpx haxqx

  . intro (haxpxaxqx : (∀ x, p x) ∧ (∀ x, q x))
    . intro (a : α)
      have haxpx : ∀ x, p x := And.left haxpxaxqx
      have hpa : p a := haxpx a
      have haxqx : ∀ x, q x := And.right haxpxaxqx
      have hqa : q a := haxqx a
      exact And.intro hpa hqa


--------------------------------------------------------------------------------------------
/-
(∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x)

1  |_ ∀ x, p x → q x
2  |  |_ ∀ x, p x
3  |  |  |_ a                                   Arbitrary 'a' (intro a) for ∀ intro
4  |  |  |  p a                                 Apply 2,3
5  |  |  |  p a → q a                           Apply 1,3
6  |  |  |  q a                                 Apply 5,4
7  |  |  ∀ x, q x                               ∀ intro 3-6
8  |  (∀ x, p x) → (∀ x, q x)                   Conditional Proof 2-7
9  (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x)   Conditional Proof 1-8
-/
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intro (haxpxqx : ∀ x, p x → q x)
  . intro (haxpx : ∀ x, p x)
    . intro (a : α)
      have hpa : p a := haxpx a
      have hpaqa : p a → q a := haxpxqx a
      exact hpaqa hpa


--------------------------------------------------------------------------------------------
/-
(∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x

1  |_ (∀ x, p x) ∨ (∀ x, q x)
2  |  |_ a                                     Arbitrary 'a' (intro a) for ∀ intro.
3  |  |  |_ ∀ x, p x
4  |  |  |  p a                                Apply 3,2
5  |  |  |  p a ∨ q a                          Or.inl 4

6  |  |  |_ ∀ x, q x
7  |  |  |  q a                                Apply 6,2
8  |  |  |  p a ∨ q a                          Or.inr 7
9  |  |  p a ∨ q a                             Or.elim 1, 3-5, 6-8
10 |  ∀ x, p x ∨ q x                           ∀ intro 2-10
11 (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x    Conditional proof 1-11
-/
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro (haxpxaxqx : (∀ x, p x) ∨ (∀ x, q x))
  . intro (a : α)
    cases haxpxaxqx with
    | inl haxpx =>
      have hpa : p a := haxpx a
      exact Or.inl hpa

    | inr haxqx =>
      have hqa : q a := haxqx a
      exact Or.inr hqa


/-
(∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x

1  |_ (∀ x, p x) ∨ (∀ x, q x)
2  |  |_ ∀ x, p x
3  |  |  |_ a
4  |  |  |  p a                              Apply 2,3
5  |  |  |  p a ∨ q a                        Or.inl 4
6  |  |  ∀ x, p x ∨ q x                      ∀ intro 3-5

7  |  |_ ∀ x, q x
8  |  |  |_ a
9  |  |  |  q a                               Apply 7,8
10 |  |  |  p a ∨ q a                         Or.inr 9
11 |  |  ∀ x, p x ∨ q x                       ∀ intro 8-10
12 |  ∀ x, p x ∨ q x                          Or.elim 1, 2-6, 7-11
13 (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x   Conditional proof 1-12
-/
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro (haxpxaxqx : (∀ x, p x) ∨ (∀ x, q x))
  cases haxpxaxqx with
  | inl haxpx =>
    intro (a : α)
    have hpa : p a := haxpx a
    exact Or.inl hpa

  | inr haxqx =>
    intro (a : α)
    have hqa : q a := haxqx a
    exact Or.inr hqa


-----------------------------------------------------------------------------------------------------------------------------
-- 2. It is often possible to bring a component of a formula outside a universal quantifier, when it does not depend on the quantified variable.
-- Try proving these (one direction of the second of these requires classical logic):

-- ### These variable assignments from the book are not really needed.
-- variable (α : Type) (p q : α → Prop)
-- variable (r : Prop)

/-
α → ((∀ _ : α, r) ↔ r)

1  |_ a : α                   Assumption (arbitrary variable of type α)
2  |  |_ (∀ _ : α, r)
3  |  |  r                    Apply 2,1 (type)
4  |  (∀ _ : α, r) → r        Conditional proof 2-3

5  |  |_ r
6  |  |  |_ α                 Assumption (arbitrary type α : Type)
7  |  |  |  r                 Reiteration 6
8  |  |  (∀ _ : α, r)         ∀ intro 6-7
9  |  r → (∀ _ :α, r)         Conditional Proof 5-8

10  α → (∀ _ : α, r) ↔ r      Conditional Proof 1-9 (Using type α)
-/
example {r} : α → ((∀ _ : α, r) ↔ r) := by
  intro (a : α)
  apply Iff.intro
  . intro (haxr : ∀ _ : α, r)
    exact (haxr a : r)

  . intro (hr : r)
    . intro (_ : α)
      exact (hr : r)

-- Kept here as an example.
example : α → ((∀ _ : α, r) ↔ r) :=
  fun a : α =>
  Iff.intro
    (fun har : ∀ _ : α, r => (har a : r) : (∀ _ : α, r) → r)
    (fun hr : r => (fun _ : α => (hr : r) : (∀ _ : α, r)) : r → (∀ _ : α, r))


/-
α → ((∀ x : α, r) ↔ r)

1  |_ a : α                   Assumption (arbitrary variable of type α)
2  |  |_ α → r                Equivalent to (∀ x : α, r)
3  |  |  r                    Apply 2,1 (type)
4  |  (α → r) → r             Conditional proof 2-3

5  |  |_ r
6  |  |  |_ α                 Assumption (arbitrary type α : Type)
7  |  |  |  r                 Reiteration 6
8  |  |  α → r                Conditional Proof 6-7 (Equivalent to '∀ intro' (∀ x : α, r))
9  |  r → α → r               Conditional Proof 5-8 (Equivalent to r → ∀ x : α, r)

10  α → (∀ x : α, r) ↔ r      Conditional Proof 1-9 (Using type α)
-/
example {r} : α → ((∀ x : α, r) ↔ r) := by
  intro a
  apply Iff.intro
  . intro (hαr : α → r)
    exact (hαr a : r)

  . intro (hr : r)
    . intro α
      exact (hr : r)

-- Kept here as an example.
example : α → ((∀ x : α, r) ↔ r) :=
  fun a : α =>
  Iff.intro
    (fun har : (α → r) => (har a : r) : (α → r) → r)
    (fun hr : r => fun _ : α => (hr : r) : r → (α → r))


-- <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<< I am here.
--------------------------------------------------------------------------------------------------------------------------------
/-
(∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r

1  |_ (∀ x, p x ∨ r)
2  |  r ∨ ¬r                              Tertio Excluso
3  |  |_ r
4  |  |  (∀ x, p x) ∨ r                   Or.inr 3

5  |  |_ ¬r
6  |  |  |_ a                             Arbitrary 'a' (fun x =>) for ∀ intro.
7  |  |  |  p a ∨ r                       Apply 1,6
8  |  |  |  |_ p a
9  |  |  |  |  p a

10 |  |  |  |_ r
11 |  |  |  |  False                      Apply 5,10
12 |  |  |  |  p a                        False.elim 11
13 |  |  |  p a                           Or.elim 7, 8-9, 10-12
14 |  |  ∀ x, p x                         ∀ Intro 6-13
15 |  |  (∀ x, p x) ∨ r                   Or.inl 14
16 |  (∀ x, p x) ∨ r                      Or.elim 2,3-4, 5-15
17 (∀ x, p x ∨ r) → (∀ x, p x) ∨ r        Conditional Proof 1-16

18 |_ (∀ x, p x) ∨ r
19 |  |_ ∀ x, p x
20 |  |  |_ a                             Arbitrary 'a' for ∀ intro
21 |  |  |  p a                           Apply 19,20
22 |  |  |  p a ∨ r                       Or.inl 4
23 |  |  ∀ x, p x ∨ r                     ∀ intro 3-5

24 |  |_ r
25 |  |  |_ a                             Arbitrary 'a' or '_' for ∀ intro
26 |  |  |  p a ∨ r                       Or.inr 24
27 |  |  ∀ a, p a ∨ r                     ∀ intro 25,27
28 |  ∀ x, p x ∨ r                        Or.elim 18, 19-23, 24-28
29 |  (∀ x, p x ∨ r) → (∀ x, p x) ∨ r     Conditional Proof 18-28

30 (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r     Iff.intro 17,29
-/
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
    (fun h =>
      Or.elim  (em r)
      (fun hr => Or.inr hr)
      (fun hnr => Or.inl
       fun a =>
         Or.elim (h a)
           (fun hpa => hpa)
           (fun hr => False.elim (hnr hr))))
    (fun h =>
      Or.elim h
      (fun hpx => fun a => Or.inl (hpx a))
      (fun hr => fun _ => Or.inr hr))

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
    (fun h =>
      match em r with
      | Or.inl hr => Or.inr hr
      | Or.inr hnr => Or.inl (fun a =>
          match h a with
          | Or.inl hpx => hpx
          | Or.inr hr => False.elim (hnr hr)))
    (fun h =>
      match h with
      | Or.inl hp => fun a => Or.inl (hp a)
      | Or.inr hr => fun _ => Or.inr hr)

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
    (fun h =>
      byCases
        (fun hr : r => Or.inr hr
        : r → (∀ x, p x) ∨ r)
        (fun hnr => Or.inl
          (fun a =>
            Or.elim (h a)
              (fun hpa : p a => hpa : p a → p a)
              (fun hr : r => False.elim (hnr hr : False) : r → p a)
          : ∀ x, p x)
        : ¬r →  (∀ x, p x) ∨ r)
    : (∀ x, p x ∨ r) → (∀ x, p x) ∨ r)
    (fun h =>
      Or.elim h
      (fun hp : ∀ x, p x => fun a => Or.inl (hp a))
      (fun hr : r => fun _ => Or.inr hr))

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
    (fun h =>
      if hr : r then
        Or.inr hr
      else
        Or.inl (fun x =>
          match h x with
          | Or.inl hpx => hpx
          | Or.inr hr' => False.elim (hr hr')))
    (fun h =>
      match h with
      | Or.inl hp => fun a => Or.inl (hp a)
      | Or.inr hr => fun a => Or.inr hr)


-----------------------------------------------------------------------------------------
/-
(∀ x, r → p x) ↔ (r → ∀ x, p x)

1  |_ (∀ x, r → p x)
2  |  |_ r
3  |  |  |_ a                         Arbitrary 'a' (fun x =>) for ∀ intro.
4  |  |  |  r → p a                   Apply 1,3
5  |  |  |  p a                       Apply 4,2
6  |  |  ∀ x, p x                     ∀ intro 3-5
7  |  r → ∀ x, p x                    Conditional Proof 2-6
8  (∀ x, r → p x) → (r → ∀ x, p x)    Conditional Proof 1-7

9  |_ r → ∀ x, p x
10 |  |_ a                            Arbitrary 'a' (fun x =>) for ∀ intro.
11 |  |  |_ r
12 |  |  |  ∀ x, p x                  Apply 9,11
13 |  |  |  p a                       Apply 12,10
14 |  |  r → p a                      Conditional Proof 3-4
15 |  ∀ x, r → p x                    ∀ intro 2-5
16 (r → ∀ x, p x) → (∀ x, r → p x)    Conditional Proof 9-15

17 (∀ x, r → p x) ↔ (r → ∀ x, p x)    Iff.intro 8,16
-/
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
    (fun h : ∀ x, r → p x => fun hr : r => fun a : α => h a hr)
    (fun h : r → ∀ x, p x => fun a : α => fun hr : r => h hr a)

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
    ((fun h : ∀ x, r → p x => (fun hr : r => (fun a : α => ((h a : r → p a) hr : p a) : ∀ x, p x) : r → ∀ x, p x))
      : (∀ x, r → p x) → (r → ∀ x, p x))
    ((fun h : r → ∀ x, p x => (fun a : α => (fun hr : r => ((h hr : ∀ x, p x) a : p a) : r → p a) : ∀ x, r → p x))
      : (r → ∀ x, p x) → (∀ x, r → p x))
