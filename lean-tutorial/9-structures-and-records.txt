https://leanprover.github.io/theorem_proving_in_lean4/structures_and_records.html#objects
structure Point (α : Type u) where
  x : α
  y : α
  deriving Repr

def p : Point Nat :=
  { x := 1, y := 2 }

#eval { p with y := 3 }  -- { x := 1, y := 3 }
#eval { p with x := 4 }  -- { x := 4, y := 2 }

structure Point3 (α : Type u) where
  x : α
  y : α
  z : α

def q : Point3 Nat :=
  { x := 5, y := 5, z := 5 }

def r : Point3 Nat :=
  { p, q with x := 6 }

-- The order of asignment is, first 'p', then any value not in 'p' is taken from 'q', and finally x value is overrided using 'with'.
example : r.x = 6 := rfl
example : r.y = 2 := rfl
example : r.z = 5 := rfl




-- ############################################################################################
-- https://leanprover.github.io/theorem_proving_in_lean4/structures_and_records.html#inheritance
structure Point (α : Type u) where
  x : α
  y : α
  z : α

structure RGBValue where
  red : Nat
  green : Nat
  blue : Nat

structure RedGreenPoint (α : Type u) extends Point α, RGBValue where
  no_blue : blue = 0

def p : Point Nat :=
  { x := 10, y := 10, z := 20 }

def rgp : RedGreenPoint Nat :=
  { p with red := 200, green := 40, blue := 0, no_blue := rfl }

example : rgp.x   = 10 := rfl
example : rgp.red = 200 := rfl

-- Extra example added
#check rgp.no_blue
example : rgp.blue = 0 := rgp.no_blue
