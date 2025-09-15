-- 1. Open a namespace Hidden to avoid naming conflicts, and use the equation compiler to define addition, multiplication, and exponentiation on the natural numbers. Then use the equation compiler to derive some of their basic properties.

-- ##########################################################################################################
-- # Definition of Natural numbers
inductive Natural where
  | cero : Natural
  | sucesor : Natural → Natural

namespace Natural
-- Defining some numbers
def uno : Natural := sucesor cero
def dos : Natural := sucesor uno
def tres : Natural := sucesor dos
def cuatro : Natural := sucesor tres


-- #################################################################################################
-- Definition of addition.
-- Init/Prelude.lean
def sumar : Natural → Natural → Natural
  | a, cero => a
  | a, sucesor b => sucesor (sumar a b)


#eval sumar cero dos
#eval sumar dos uno
#eval 0

def ceroMasDos : sumar cero dos = dos := rfl

/- Alternative definition of sumar.
def sumar (m n : Natural) : Natural :=
match m with
| Natural.cero => n
| Natural.sucesor m => Natural.sucesor (sumar2 m n)
-/

-- # Properties of addition.
-- ## 1) Identity element.
-- Init/Core.lean
theorem sumar_cero (n : Natural) : sumar n cero = n := rfl

theorem cero_sumar (n : Natural) : sumar cero n = n := by
  induction n with
  | cero => rfl
  | sucesor n ih =>
  calc sumar cero (sucesor n)
  _ = sucesor (sumar cero n) := rfl
  _ = sucesor n := by rw [ih]

-- Init/Data/Nat/Basic.lean (adapted to Natural)
theorem cero_sumar2 : ∀ (n : Natural), sumar cero n = n
  | cero => rfl
  | sucesor n => congrArg sucesor (cero_sumar2 n)


-- ## 2) Successor property.
theorem sucesor_sumar : ∀ (n m : Natural), sumar (sucesor n) m = sucesor (sumar n m)
  | n,  cero      => rfl -- base case
  | n,  sucesor m =>     -- inductive step
    calc
      sumar (sucesor n) (sucesor m)
        = sucesor (sumar (sucesor n) m) := by rw [sumar] -- unfold definition
      _ = sucesor (sucesor (sumar n m)) := by rw [sucesor_sumar n m] -- inductive hypothesis
      _ = sucesor (sumar n (sucesor m)) := by rw [sumar]

-- Init/Data/Nat/Basic.lean (adapted to Natural)
theorem sucesor_sumar2 : ∀ (n m : Natural), sumar (sucesor n) m = sucesor (sumar n m)
  | _, cero => rfl
  | n, sucesor m => congrArg sucesor (sucesor_sumar n m)

-- Init/Data/Nat/Basic.lean
theorem sumar_sucesor (n m : Natural) : sumar n (sucesor m) = sucesor (sumar n m) := rfl


-- ## 3) Associativity.
theorem sumar_asociativa (n m k : Natural) : sumar (sumar n m) k = sumar n (sumar m k) := by
  induction k with
  | cero => rfl
  | sucesor k ih =>
  calc sumar (sumar n m) (sucesor k)
  _ = sucesor (sumar (sumar n m) k) := rfl
  _ = sucesor (sumar n (sumar m k)) := by rw [ih]
  _ = sumar n (sumar m (sucesor k)) := rfl

-- Init/Data/Nat/Basic.lean
theorem add_assoc : ∀ (n m k : Natural), sumar (sumar n m) k = sumar n (sumar m k)
  | _, _, cero      => rfl
  | n, m, sucesor k => congrArg sucesor (sumar_asociativa n m k)


-- ## 4) Commutativity.
theorem sumar_conmutativa (n m : Natural) :sumar n m = sumar m n := by
  induction n with
  | cero =>
  calc sumar cero m
  _ = m := by rw [Natural.cero_sumar]
  _ = Natural.sumar m Natural.cero := rfl
  | sucesor n ih =>
  calc sumar (sucesor n) m
  _ = sucesor (sumar n m) := by rw [sucesor_sumar]
  _ = sucesor (sumar m n) := by rw [ih]
  _ = sumar m (sucesor n) := by rw [sumar]


theorem MyEq.symm {α : Sort u} {a b : α} (h : Eq a b) : Eq b a := h ▸ rfl

-- Init/Data/Nat/Basic.lean (adapted to Natural)
theorem sumar_conmutativa2 : ∀ (n m : Natural), sumar n m = sumar m n
  | n, cero => MyEq.symm (Natural.cero_sumar n)
  | n, sucesor m => by
    have : sucesor (sumar n m) = sucesor (sumar m n) := by apply congrArg; apply Natural.sumar_conmutativa2
    rw [sucesor_sumar m n]
    apply this


-- #### Sumar derecha conmutativa
-- Init/Data/Nat/Basic.lean
protected theorem add_right_comm (n m k : Nat) : (n + m) + k = (n + k) + m := by
  rw [Nat.add_assoc, Nat.add_comm m k, ← Nat.add_assoc]

theorem sumar_derecha_commutativa (n m k : Natural) : sumar (sumar n m) k = sumar (sumar n k) m := by
  rw [sumar_asociativa, sumar_conmutativa m k, ← sumar_asociativa]

theorem sumar_derecha_commutativa2 (n m k : Natural) : sumar (sumar n m) k = sumar (sumar n k) m := by
  calc
    sumar (sumar n m) k
    _ = sumar n (sumar m k) := by rw [sumar_asociativa]
    _ = sumar n (sumar k m) := by rw [sumar_conmutativa m k]
    _ = sumar (sumar n k) m := by rw [sumar_asociativa]

-- #### Sumar izquierda conmutativa
-- Init/Data/Nat/Basic.lean
theorem add_left_comm2 (n m k : Nat) : n + (m + k) = m + (n + k) := by
  rw [← Nat.add_assoc, Nat.add_comm n m, Nat.add_assoc]

theorem sumar_izquierda_conmutativa (n m k : Natural) : sumar n (sumar m k) = sumar m (sumar n k) := by
  rw [← sumar_asociativa, sumar_conmutativa n m, sumar_asociativa]

theorem sumar_izquierda_conmutativa2 (n m k : Natural) : sumar n (sumar m k) = sumar m (sumar n k) := by
  calc
    sumar n (sumar m k)
      = sumar (sumar n m) k         := by rw [← sumar_asociativa]
    _ = sumar (sumar m n) k         := by rw [sumar_conmutativa n m]
    _ = sumar m (sumar n k)         := by rw [sumar_asociativa]


-- #################################################################################################
-- Definition of multiplication.
-- Init/Prelude.lean
def multiplicar : Natural → Natural → Natural
  | _, cero => cero
  | a, sucesor b => sumar (multiplicar a b) a

-- # Properties of multiplication.
#eval multiplicar cero dos
#eval multiplicar dos cero
#eval multiplicar dos dos
#eval multiplicar cuatro tres

-- ## 1) Identity element.
theorem uno_multiplicar (n : Natural) : multiplicar uno n = n := by
induction n with
  | cero => rfl
  | sucesor n ih =>
  calc multiplicar uno (sucesor n)
  _ = sumar (multiplicar uno n) uno := rfl
  _ = sumar n uno  := by rw [ih]
  _ = sucesor n := by rfl

-- Init/Data/Nat/Basic.lean (Not adapted to Natural).
protected theorem one_mul (n : Nat) : 1 * n = n :=
  Nat.mul_comm n 1 ▸ Nat.mul_one n

-- Init/Data/Nat/Basic.lean
theorem multiplicar_uno : ∀ (n : Natural), multiplicar n uno = n := cero_sumar

theorem multiplicar_uno2 (n : Natural) : multiplicar n uno = n := cero_sumar n

theorem multiplicar_uno3 (n : Natural) : multiplicar n uno = n := by
  induction n with
  | cero => rfl
  | sucesor n ih =>
    calc multiplicar (sucesor n) uno
    _ = sumar (multiplicar n uno) uno := rfl
    _ = sumar n uno := by rw [ih]
    _ = sucesor n := by rfl

theorem multiplicar_sucesor_cero : ∀ (n : Natural), multiplicar n (sucesor cero) = n := cero_sumar -- cero_sumar

theorem multiplicar_sucesor_cero2 (n : Natural) : multiplicar n (sucesor cero) = n := by
  induction n with
  | cero => rfl
  | sucesor n ih =>
    calc multiplicar (sucesor n) (sucesor cero)
    _ = sumar (multiplicar n (sucesor cero)) (sucesor cero) := rfl
    _ = sumar n (sucesor cero) := by rw [ih]
    _ = sucesor n := by rfl

theorem multiplicar_sucesor_cero3 : ∀ (n : Natural), multiplicar n (sucesor cero) = n := by
  intro n
  induction n with
  | cero => rfl
  | sucesor n ih =>
    calc multiplicar (sucesor n) (sucesor cero)
    _ = sumar (multiplicar n (sucesor cero)) (sucesor cero) := rfl
    _ = sumar n (sucesor cero) := by rw [ih]
    _ = sucesor n := by rfl

-- ## 2) Property of 0.
-- Init/Data/Nat/Basic.lean
theorem cero_multiplicar : ∀ (n : Natural), multiplicar cero n = cero := by
  intro n
  induction n with
  | cero => rfl
  | sucesor n ih =>
  calc multiplicar cero (sucesor n)
  _ = sumar (multiplicar cero n) cero := by rw [multiplicar]
  _ = sumar cero cero := by rw [ih]
  _ = cero := rfl

theorem cero_multiplicar2 (n : Natural) : multiplicar cero n = cero := by
  induction n with
  | cero => rfl
  | sucesor n ih =>
  calc multiplicar cero (sucesor n)
  _ = sumar (multiplicar cero n) cero := by rw [multiplicar]
  _ = sumar cero cero := by rw [ih]
  _ = cero := by rw [sumar]

-- Init/Data/Nat/Basic.lean
theorem multiplicar_cero (n : Natural) : multiplicar n cero = cero := rfl

theorem multiplicar_cero2 : ∀ (n : Natural), multiplicar n cero = cero := by
  intro n
  induction n with
  | cero => rfl
  | sucesor n ih =>
    calc
      multiplicar (sucesor n) cero
        = sumar cero (multiplicar n cero) := rfl
      _ = sumar cero cero := by rw [ih]
      _ = cero := rfl

-- ## 3) Multiplication by successor.
-- Init/Data/Nat/Basic.lean
theorem multiplicar_sucesor (n m : Natural) : multiplicar n (sucesor m) = sumar (multiplicar n m) n := rfl

-- Init/Data/Nat/Basic.lean
theorem sucesor_multiplicar (n m : Natural) : multiplicar (sucesor n) m = sumar (multiplicar n m) m := by
  induction m with
  | cero => rfl
  | sucesor m ih =>
    calc
      multiplicar (sucesor n) (sucesor m)
        = sumar (multiplicar (sucesor n) m) (sucesor n) := by rw [multiplicar_sucesor]
      _ = sucesor (sumar (multiplicar (sucesor n) m) n) := by rw [sumar_sucesor]
      _ = sucesor (sumar (sumar (multiplicar n m) m) n) := by rw [ih]
      _ = sucesor (sumar (sumar (multiplicar n m) n) m) := by rw [sumar_derecha_commutativa]
      _ = sucesor (sumar (multiplicar n (sucesor m)) m) := by rw [multiplicar_sucesor]
      _ = sumar (multiplicar n (sucesor m)) (sucesor m) := by rw [sumar_sucesor]

-- Init/Data/Nat/Basic.lean
theorem succ_mul (n m : Nat) : (Nat.succ n) * m = (n * m) + m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Nat.mul_succ, Nat.add_succ, ih, Nat.mul_succ, Nat.add_succ, Nat.add_right_comm]

theorem succ_mul2 (n m : Nat) : (Nat.succ n) * m = (n * m) + m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    calc
      Nat.succ n * Nat.succ m
        = (Nat.succ n) * m + (Nat.succ n) := by rw [Nat.mul_succ]
      _ = Nat.succ (Nat.succ n * m + n)   := by rw [Nat.add_succ]
      _ = Nat.succ (n * m + m + n)        := by rw [ih]
      _ = Nat.succ (n * m + n + m)        := by rw [Nat.add_right_comm]
      _ = Nat.succ (n * (Nat.succ m) + m) := by rw [Nat.mul_succ]
      _ = (n * Nat.succ m) + Nat.succ m   := by rw [Nat.add_succ]

-- ## 4) Commutative property
theorem multiplicar_conmutativa (m n : Natural) : multiplicar m n = multiplicar n m := by
  induction n with
  | cero =>
    -- Base case: multiplicar m 0 = 0 = multiplicar 0 m
    rw [cero_multiplicar, multiplicar_cero]
  | sucesor n ih =>
    calc
      multiplicar m (sucesor n)
        = sumar (multiplicar m n) m := by rw [multiplicar]
      _ = sumar (multiplicar n m) m := by rw [ih]
      _ = multiplicar (sucesor n) m := by rw [sucesor_multiplicar]

theorem multiplicar_conmutativa2 : ∀ (m n : Natural), multiplicar m n = multiplicar n m := by
  intro m n
  induction n with
  | cero =>
    -- Base case: multiplicar m 0 = 0 = multiplicar 0 m
    rw [cero_multiplicar, multiplicar_cero]
  | sucesor n ih =>
    calc
      multiplicar m (sucesor n)
        = sumar (multiplicar m n) m := by rw [multiplicar]
      _ = sumar (multiplicar n m) m := by rw [ih]
      _ = multiplicar (sucesor n) m := by rw [sucesor_multiplicar]

-- Init/Data/Nat/Basic.lean
theorem mul_comm : ∀ (n m : Nat), n * m = m * n
  | n, 0      => (Nat.zero_mul n).symm ▸ (Nat.mul_zero n).symm ▸ rfl
  | n, Nat.succ m => (Nat.mul_succ n m).symm ▸ (Nat.succ_mul m n).symm ▸ (Nat.mul_comm n m).symm ▸ rfl

-- Init/Data/Nat/Basic.lean (adapted to Natural)
theorem mul_comm2 : ∀ (n m : Natural), multiplicar n m = multiplicar m n
  | n, cero      => (cero_multiplicar n).symm ▸ (multiplicar_cero n).symm ▸ rfl
  | n, sucesor m => (multiplicar_sucesor n m).symm ▸ (sucesor_multiplicar m n).symm ▸ (Natural.mul_comm2 n m).symm ▸ rfl


-- ## 5) Distributive property
-- Init/Data/Nat/Basic.lean:227
theorem left_distrib (n m k : Nat) : n * (m + k) = n * m + n * k := by
  induction n with
  | zero      => repeat rw [Nat.zero_mul]
  | succ n ih => simp [succ_mul, ih]; rw [Nat.add_assoc, Nat.add_assoc (n*m)]; apply congrArg; apply Nat.add_left_comm

theorem izquierda_distributiva (n m k : Natural) : multiplicar n (sumar m k) = sumar (multiplicar n m) (multiplicar n k) := by
  induction n with
  | cero =>
    calc
      multiplicar cero (sumar m k)
        = cero := by rw [cero_multiplicar]
      _ = sumar cero cero := by rw [sumar_cero]
      _ = sumar cero (multiplicar cero k) := by rw [cero_multiplicar]
      _ = sumar (multiplicar cero m) (multiplicar cero k) := by rw [cero_multiplicar m]
  | sucesor n ih =>
    calc
      multiplicar (sucesor n) (sumar m k)
        = sumar (multiplicar n (sumar m k)) (sumar m k) := by rw [sucesor_multiplicar]
      _ = sumar (sumar (multiplicar n m) (multiplicar n k)) (sumar m k) := by rw [ih]
      _ = sumar (multiplicar n m) (sumar (multiplicar n k) (sumar m k)) := by rw [sumar_asociativa]
      _ = sumar (multiplicar n m) (sumar (sumar m k) (multiplicar n k)) := by rw [sumar_conmutativa (sumar m k)]
      _ = sumar (multiplicar n m) (sumar m (sumar k (multiplicar n k))) := by rw [sumar_asociativa]
      _ = sumar (multiplicar n m) (sumar m (sumar (multiplicar n k) k)) := by rw [sumar_conmutativa (multiplicar n k)]
      _ = sumar (sumar (multiplicar n m) m) (sumar (multiplicar n k) k) := by rw [sumar_asociativa]
      _ = sumar (sumar (multiplicar n m) m) (multiplicar (sucesor n) k) := by rw [sucesor_multiplicar n k]
      _ = sumar (multiplicar (sucesor n) m) (multiplicar (sucesor n) k) := by rw [sucesor_multiplicar n m]

-- ## 6) Associative property
-- Init/Data/Nat/Basic.lean
theorem mul_assoc : ∀ (n m k : Nat), (n * m) * k = n * (m * k)
  | _, _, 0      => rfl
  | n, m, Nat.succ k => by simp [Nat.mul_succ, Nat.mul_assoc n m k, Nat.left_distrib]

theorem multiplicar_asociativa : ∀ (n m k: Natural), multiplicar (multiplicar n m) k = multiplicar n (multiplicar m k)
  | _, _, cero      => rfl
  | n, m, sucesor k =>
    calc
      multiplicar (multiplicar n m) (sucesor k)
        = sumar (multiplicar (multiplicar n m) k) (multiplicar n m) := by rw [multiplicar_sucesor]
      _ = sumar (multiplicar n (multiplicar m k)) (multiplicar n m) := by rw [multiplicar_asociativa n m k]
      _ = multiplicar n (sumar (multiplicar m k) m) := by rw [izquierda_distributiva]
      _ = multiplicar n (multiplicar m (sucesor k)) := by rw [multiplicar_sucesor]

theorem multiplicar_asociativa2 (n m k : Natural) :
  multiplicar n (multiplicar m k) = multiplicar (multiplicar n m) k := by
  induction k with
  | cero =>
    rw [multiplicar_cero, multiplicar_cero, multiplicar_cero]
  | sucesor k ih =>
    calc
      multiplicar n (multiplicar m (sucesor k))
        = multiplicar n (sumar (multiplicar m k) m) := by rw [multiplicar_sucesor]
      _ = sumar (multiplicar n (multiplicar m k)) (multiplicar n m) := by rw [izquierda_distributiva]
      _ = sumar (multiplicar (multiplicar n m) k) (multiplicar n m) := by rw [ih]
      _ = multiplicar (multiplicar n m) (sucesor k) := by rw [multiplicar_sucesor]


-- ##############################################################################################################
-- Definition of exponentiation.
def potencia (x y : Natural) : Natural :=
  match y with
  | cero => sucesor Natural.cero
  | sucesor y => multiplicar x (potencia x y)


-- # Properties of exponentiation.
#eval potencia cero Natural.cero
#eval potencia cero cuatro
#eval potencia dos cero
#eval potencia uno cero
#eval potencia dos tres

-- ## Properties of exponentiation
-- 1) Zero exponent rule: x^0 = 1
theorem potencia_cero (x : Natural) : potencia x cero = sucesor cero := rfl

-- 2) Product of powers: x^m * x^n = x^(m + n)
theorem potencia_producto (x m n : Natural) : multiplicar (potencia x m) (potencia x n) = potencia x (sumar m n) := by
  induction n with
  | cero =>
    calc
      multiplicar (potencia x m) (potencia x cero)
        = multiplicar (potencia x m) (sucesor cero) := by rw [potencia]
      _ = (potencia x m) := by rw [multiplicar_sucesor_cero]
      _ = potencia x (sumar m cero) := by rw [sumar_cero]
  | sucesor n ih =>
    calc
      multiplicar (potencia x m) (potencia x (sucesor n))
        = multiplicar (potencia x m) (multiplicar x (potencia x n)) := by rw [potencia]
      _ = multiplicar (potencia x m) (multiplicar (potencia x n) x) := by rw [multiplicar_conmutativa x]
      _ = multiplicar (multiplicar (potencia x m) (potencia x n)) x := by rw [multiplicar_asociativa]
      _ = multiplicar (potencia x (sumar m n)) x := by rw [ih]
      _ = multiplicar x (potencia x (sumar m n)) := by rw [multiplicar_conmutativa]
      _ = potencia x (sucesor (sumar m n)) := by rw [potencia]
      _ = potencia x (sumar m (sucesor n)) := by rw [sumar_sucesor]

-- 3) Power of a product: (x * y)^n = x^n * y^n =
theorem producto_potencia (x y n : Natural) : potencia (multiplicar x y) n = multiplicar (potencia x n) (potencia y n) := by
  induction n with
  | cero =>
    calc
      potencia (multiplicar x y) cero
        = sucesor cero := by rw [potencia]
      _ = multiplicar (sucesor cero) (sucesor cero) := by rw [multiplicar_sucesor_cero]
      _ = multiplicar (potencia x cero) (sucesor cero) := by rw [potencia]
      _ = multiplicar (potencia x cero) (potencia y cero) := by rw [←potencia]
  | sucesor n ih =>
    calc
      potencia (multiplicar x y) (sucesor n)
        = multiplicar (multiplicar x y) (potencia (multiplicar x y) n) := by rw [potencia]
      _ = multiplicar (multiplicar x y) (multiplicar (potencia x n) (potencia y n)) := by rw [ih]
      _ = multiplicar (multiplicar (multiplicar x y) (potencia x n)) (potencia y n) := by rw [←multiplicar_asociativa]
      _ = multiplicar (multiplicar x (multiplicar y (potencia x n))) (potencia y n) := by simp [multiplicar_asociativa]
      _ = multiplicar (multiplicar x (multiplicar (potencia x n) y)) (potencia y n) := by simp [multiplicar_conmutativa]
      _ = multiplicar (multiplicar (multiplicar x (potencia x n)) y) (potencia y n) := by rw [←multiplicar_asociativa]
      _ = multiplicar (multiplicar x (potencia x n)) (multiplicar y (potencia y n)) := by rw [multiplicar_asociativa]
      _ = multiplicar (potencia x (sucesor n)) (multiplicar y (potencia y n)) := by rw [potencia]
      _ = multiplicar (potencia x (sucesor n)) (potencia y (sucesor n)) := by rw [←potencia]

-- 4) Power of a power: (x^m)^n = x^(m * n)
theorem potencia_potencia (x m n : Natural) : potencia (potencia x m) n = potencia x (multiplicar m n) := by
  induction n with
  | cero =>
    calc
      potencia (potencia x m) cero
        = sucesor cero := by rw [potencia]
      _ = potencia x (cero) := by rw [potencia]
      _ = potencia x (multiplicar m cero) := by rw [multiplicar]
  | sucesor n ih =>
    calc
      potencia (potencia x m) (sucesor n)
        = multiplicar (potencia x m) (potencia (potencia x m) n) := by rw [potencia]
      _ = multiplicar (potencia x m) (potencia x (multiplicar m n)) := by rw [ih]
      _ = potencia x (sumar m (multiplicar m n)) := by rw [potencia_producto]
      _ = potencia x (sumar (multiplicar m n) m) := by rw [sumar_conmutativa]
      _ = potencia x (multiplicar m (sucesor n)) := by rw [multiplicar_sucesor]

-- Init/Data/Nat/Lemmas.lean
theorem pow_mul (a m n : Nat) : a ^ (m * n) = (a ^ m) ^ n := by
  induction n with
  | zero => rw [Nat.mul_zero, Nat.pow_zero, Nat.pow_zero]
  | succ _ ih => rw [Nat.mul_succ, Nat.pow_add, Nat.pow_succ, ih]

theorem pow_mul' (a m n : Nat) : a ^ (m * n) = (a ^ m) ^ n := by
  induction n with
  | zero =>
    calc
      a ^ (m * 0)
        = a ^ 0 := by rw [Nat.mul_zero]
      _ = 1 := by rw [Nat.pow_zero]
      _ = (a ^ m) ^ 0 := by rw [Nat.pow_zero]
  | succ n ih =>
    calc
      a ^ (m * Nat.succ n)
        = a ^ (m * n + m) := by rw [Nat.mul_succ]
      _ = a ^ (m * n) * a ^ m := by rw [Nat.pow_add]
      _ = (a ^ m) ^ n * a ^ m := by rw [ih]
      _ = (a ^ m) ^ Nat.succ n := by rw [Nat.pow_succ]

end Natural

