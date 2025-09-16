-- https://leanprover.github.io/theorem_proving_in_lean4/interacting_with_lean.html#more-on-implicit-arguments

def reflexive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ (a : α), r a a

def symmetric {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b : α}, r a b → r b a

def transitive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b c : α}, r a b → r b c → r a c

def euclidean {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b c : α}}, r a b → r a c → r b c

-- Variations on th2
theorem th2 {α : Type u} {r : α → α → Prop}
            (symmr : symmetric r) (euclr : euclidean r)
            : transitive r :=
  fun {a b c : α} =>
  fun (rab : r a b) (rbc : r b c) =>
  euclr (symmr rab) rbc

theorem th2a {α : Type u} {r : α → α → Prop}
            (symmr : symmetric r) (euclr : euclidean r)
            : transitive r :=
  fun {a b c : α} =>
  fun (rab : r a b) (rbc : r b c) =>
  show r a c from euclr (symmr rab) rbc

theorem th2b {α : Type u} {r : α → α → Prop}
            (symmr : symmetric r) (euclr : euclidean r)
            : transitive r :=
    λ {a b c} (rab : r a b) (rbc : r b c) => euclr (symmr rab) rbc

theorem th2c {α : Type u} {r : α → α → Prop}
            (symmr : symmetric r) (euclr : euclidean r)
            : transitive r :=
  λ {a b c} => λ (rab : r a b) => λ (rbc : r b c) => euclr (symmr rab) rbc
