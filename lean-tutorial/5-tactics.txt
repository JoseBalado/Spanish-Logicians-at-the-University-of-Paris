-- https://lean-lang.org/theorem_proving_in_lean4/tactics.html#entering-tactic-mode
-- (hp : p) (hq : q) : p ∧ q ∧ p
-- Dot notation really does nothing, just allows to indent the code:
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  . exact hp
  . apply And.intro
    . exact hq
    . exact hp

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  . exact hp
  . apply And.intro
    exact hq
    . exact hp

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  . exact hp
  . apply And.intro
    exact hq
    exact hp

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  . apply And.intro
    exact hq
    exact hp

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp


--------------------------------------------------------------------------------
-- (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x
example (α : Type) (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro ⟨x, hpq⟩
  apply Or.elim hpq
  . intro hp
    apply Exists.intro
    apply Or.inr
    exact hp
  . intro hq
    apply Exists.intro
    apply Or.inl
    exact hq

example (α : Type) (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro ⟨x, hpq⟩
  apply Or.elim hpq
  intro hp
  apply Exists.intro
  apply Or.inr
  exact hp
  . intro hq
    apply Exists.intro
    apply Or.inl
    exact hq

example (α : Type) (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro ⟨x, hpq⟩
  apply Or.elim hpq
  intro hp
  apply Exists.intro
  apply Or.inr
  exact hp
  intro hq
  apply Exists.intro
  apply Or.inl
  exact hq



////////////////////////////////////////////////////////////////////////////////////
-- https://lean-lang.org/theorem_proving_in_lean4/tactics.html#basic-tactics


-- p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    apply Or.elim (And.right h)
    . intro hq
      apply Or.inl
      apply And.intro
      . exact And.left h
      . exact hq
    . intro hr
      apply Or.inr
      apply And.intro
      . exact And.left h
      . exact hr
  . intro h
    apply Or.elim h
    . intro hpq
      apply And.intro
      . exact And.left hpq
      . apply Or.inl
        exact And.right hpq
    . intro hpr
      apply And.intro
      . exact And.left hpr
      . apply Or.inr
        exact And.right hpr

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  intro h
  apply Or.elim (And.right h)
  intro hq
  apply Or.inl
  apply And.intro
  exact And.left h
  exact hq
  intro hr
  apply Or.inr
  apply And.intro
  exact And.left h
  exact hr
  intro h
  apply Or.elim h
  intro hpq
  apply And.intro
  exact And.left hpq
  apply Or.inl
  exact And.right hpq
  intro hpr
  apply And.intro
  exact And.left hpr
  apply Or.inr
  exact And.right hpr


-------------------------------------------------------------------------------
example (α : Type) (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro ⟨x, hpq⟩
  apply Or.elim hpq
  . intro hp
    apply Exists.intro
    apply Or.inr
    exact hp
  . intro hq
    apply Exists.intro
    apply Or.inl
    exact hq


-- Removing revert x and intro y, from the original example. rfl is all that is needed.
example (x : Nat) : x = x := by
  -- revert x
  -- goal is ⊢ ∀ (x : Nat), x = x
  -- intro y
  -- goal is y : Nat ⊢ y = y
  rfl




////////////////////////////////////////////////////////////////////////////////
-- https://lean-lang.org/theorem_proving_in_lean4/tactics.html#more-tactics
example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  cases h with
  | intro hp hq => constructor; exact hq; exact hp


-- equivalent to
example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  cases h with
  | intro hp hq =>
    apply And.intro
    exact hq
    exact hp

-----------------------------------------------------------------------------------------
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    match h with
    | ⟨_, Or.inl _⟩ => apply Or.inl; constructor <;> assumption
    | ⟨_, Or.inr _⟩ => apply Or.inr; constructor <;> assumption
  . intro h
    match h with
    | Or.inl ⟨hp, hq⟩ => constructor; exact hp; apply Or.inl; exact hq
    | Or.inr ⟨hp, hr⟩ => constructor; exact hp; apply Or.inr; exact hr

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    match h with
    -- | ⟨_, Or.inl _⟩ => apply Or.inl; constructor <;> assumption
    | ⟨hp, Or.inl hq⟩ => apply Or.inl; constructor <;> assumption
    -- | ⟨_, Or.inr _⟩ => apply Or.inr; constructor <;> assumption
    | ⟨hp, Or.inr hr⟩ => apply Or.inr; constructor; exact hp; exact hr
  . intro h
    match h with
    | Or.inl ⟨hp, hq⟩ => constructor; exact hp; apply Or.inl; exact hq
    -- | Or.inr ⟨hp, hr⟩ => constructor; exact hp; apply Or.inr; exact hr
    | Or.inr ⟨_, _⟩ => constructor; assumption; apply Or.inr; assumption -- using _ to ignore the variables




/////////////////////////////////////////////////////////////////////////////////////////////////
-- https://leanprover.github.io/theorem_proving_in_lean4/tactics.html#rewriting

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_comm b, ← Nat.add_assoc]

example (a b c : Nat) : a + b + c = a + c + b := by
  calc
    a + b + c = a + (b + c)   := by rw [Nat.add_assoc]
            _ = a + (c + b)   := by rw [Nat.add_comm b c]
            _ = a + c + b     := by rw [Nat.add_assoc]

example (a b c : Nat) : a + b + c = a + c + b := by
  apply Eq.trans (Nat.add_assoc a b c)
  apply Eq.trans (congrArg (Nat.add a) (Nat.add_comm b c))
  apply Eq.symm
  apply Nat.add_assoc


//////////////////////////////////////////////////////////////////////////////////////////////////////////////
-- https://leanprover.github.io/theorem_proving_in_lean4/tactics.html#using-the-simplifier

attribute [local simp] Nat.mul_comm Nat.mul_assoc Nat.mul_left_comm
attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm
example (w x y z : Nat) (p : Nat → Prop)
        : x * y + z * w * x = x * w * z + y * x := by
  simp

example (w x y z : Nat) : x * y + z * w * x = x * w * z + y * x :=
   calc x * y + z * w * x
    _ = y * x + z * w * x := by rw [Nat.mul_comm]
    _ = y * x + z * (w * x) := by rw [Nat.mul_assoc]
    _ = y * x + z * (x * w) := by rw [Nat.mul_comm x]
    _ = y * x + (x * w) * z := by rw [Nat.mul_comm z]
    _ = x * w * z + y * x := by rw [Nat.add_comm]



----------------------------------------------------------------------------------------------------------
example {m n : Nat} (h : n = 1) (h' : 0 = m) : (f m n) = n := by
  simp [h, ←h', f]

example {m n : Nat} (h : n = 1) (h' : 0 = m) : (f m n) = n :=
    calc f m n = m + n + m := by rw [f] -- by rfl
        _ = 0 + n + m := by rw [h']
        _ = 0 + n + 0 := by rw [h']
        _ = n + 0 := by rw [Nat.zero_add]
        _ = n := by rw [Nat.add_zero]


----------------------------------------------------------------------------------------------
example (u w x y z : Nat) (h₁ : x = y + z) (h₂ : w = u + x)
        : w = z + y + u := by
  simp [*, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

example (u w x y z : Nat) (h₁ : x = y + z) (h₂ : w = u + x)
        : w = z + y + u := by
     rw [h₂]
     rw [h₁]
     rw [Nat.add_assoc]
     rw [Nat.add_comm]
     rw [Nat.add_left_comm]
     rw [Nat.add_assoc]


example (u w x y z : Nat) (h₁ : x = y + z) (h₂ : w = u + x) : w = z + y + u := 
  calc w
    _ = u + x := by rw [h₂]
    _ = u + (y + z) := by rw [h₁]
    _ = y + z + u := by rw [Nat.add_comm]
    _ = z + y + u := by rw [Nat.add_comm z]


----------------------------------------------------------------------------
example (p q : Prop) (hp : p) : p ∧ q ↔ q := by
  simp [*]

example (p q : Prop) (hp : p) : p ∧ q ↔ q := by
  apply Iff.intro
  -- Prove `p ∧ q → q`
  intro h
  exact h.right
  -- Prove `q → p ∧ q`
  intro hq
  exact And.intro hp hq


----------------------------------------------------------------------------
example (p q : Prop) (hp : p) : p ∨ q := by
  simp [*]

example (p q : Prop) (hp : p) : p ∨ q := by
  exact Or.inl hp

example (p q : Prop) (hp : p) : p ∨ q := by
  apply Or.intro_left -- Or.intro_left needs exact hp
  exact hp

example (p q : Prop) (hp : p) : p ∨ q := by
  apply Or.inl hp

example (p q : Prop) (hp : p) : p ∨ q := 
  Or.inl hp

example (p q : Prop) (hp : p) : p ∨ q := 
  Or.intro_left q hp

-- Lean assumes that (p q : Prop) 
example (hp : p) : p ∨ q := 
  Or.intro_left q hp


-------------------------------------------------------------------------------
example (p q r : Prop) (hp : p) (hq : q) : p ∧ (q ∨ r) := by
  simp [*]

example (p q r : Prop) (hp : p) (hq : q) : p ∧ (q ∨ r) := by
  have hqr := Or.intro_left r hq
  exact And.intro hp hqr

example (p q r : Prop) (hp : p) (hq : q) : p ∧ (q ∨ r) := by
  apply And.intro
  -- Prove `p`
  exact hp
  -- Prove `q ∨ r`
  apply Or.intro_left
  exact hq

example (p q r : Prop) (hp : p) (hq : q) : p ∧ (q ∨ r) := by
  apply And.intro
  -- Prove `p`
  exact hp
  -- Prove `q ∨ r`
  exact Or.inl hq


----------------------------------------------------------------------------------
example (u w x x' y y' z : Nat) (p : Nat → Prop)
        (h₁ : x + 0 = x') (h₂ : y + 0 = y')
        : x + y + 0 = x' + y' := by
  simp at *
  simp [*]

example (x x' y y' : Nat)
        (h₁ : x + 0 = x') (h₂ : y + 0 = y')
        : x + y + 0 = x' + y' := by
  calc  x + y + 0
    _ = x + (y + 0) := by rw [Nat.add_assoc]
    _ = x + y' := by rw [h₂]
    _ = x + 0 + y' := by rw [Nat.add_zero]
    _ = x' + y' := by rw [h₁]

example (x x' y y' : Nat)
        (h₁ : x + 0 = x') (h₂ : y + 0 = y')
        : x + y + 0 = x' + y' := by
        rw [Nat.add_assoc]
        rw [h₂]
        rw [←Nat.add_zero x]
        rw [h₁]

example (x x' y y' : Nat) (h₁ : x + 0 = x') (h₂ : y + 0 = y') : x + y + 0 = x' + y' :=
 h₁ ▸ h₂ ▸ rfl


--------------------------------------------------------------------------------------
def mk_symm (xs : List α) :=
 xs ++ xs.reverse

theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

theorem reverse_mk_symm2 (xs : List α) : (mk_symm xs).reverse = mk_symm xs :=
  by rw [mk_symm, reverse_append, List.reverse_reverse]

theorem reverse_mk_symm3 (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs :=
        calc (mk_symm xs).reverse
          _ = (xs ++ xs.reverse).reverse := by rw [mk_symm]
          _ = xs.reverse.reverse ++ xs.reverse := by rw [reverse_append]
          _ = xs ++ xs.reverse := by rw [List.reverse_reverse]

theorem reverse_mk_symm4 (xs : List α) : (mk_symm xs).reverse = mk_symm xs :=
  List.recOn xs
    (by simp [mk_symm])
    (fun hd tl ih => by simp [mk_symm, ih])


----------------------------------------------------------------------------------------
def mk_symm (xs : List α) :=
 xs ++ xs.reverse

theorem reverse_mk_symm (xs : List α)
       : (mk_symm xs).reverse = mk_symm xs := by
 simp [mk_symm]

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp [reverse_mk_symm]

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  calc  (xs ++ mk_symm ys).reverse
    _ = (xs ++ (ys ++ ys.reverse)).reverse := by rw [mk_symm]
    _ = (ys ++ ys.reverse).reverse ++ xs.reverse := by rw [reverse_append]
    _ = (ys.reverse.reverse ++ ys.reverse) ++ xs.reverse := by rw [List.reverse_append]
    _ = (ys ++ ys.reverse) ++ xs.reverse := by rw [List.reverse_reverse]
    _ = (mk_symm ys) ++ xs.reverse := by rw [mk_symm]

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
    rw [mk_symm]
    rw [reverse_append]
    rw [List.reverse_append]
    rw [List.reverse_reverse]


---------------------------------------------------------------------------------------
def mk_symm (xs : List α) :=
 xs ++ xs.reverse

theorem reverse_mk_symm (xs : List α)
       : (mk_symm xs).reverse = mk_symm xs := by
 simp [mk_symm]

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp [reverse_mk_symm] at h; assumption

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  have : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
    rw [mk_symm]
    rw [reverse_append]
    rw [List.reverse_append]
    rw [List.reverse_reverse]
  rw [this] at h
  exact h









