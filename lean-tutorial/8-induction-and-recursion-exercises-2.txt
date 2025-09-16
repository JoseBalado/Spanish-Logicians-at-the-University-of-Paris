-- 2. Similarly, use the equation compiler to define some basic operations on lists (like the reverse function) and prove theorems about lists by induction (such as the fact that reverse (reverse xs) = xs for any list xs).

#eval List.reverse [1, 2, 3, 4, 5]

def inversa {α : Type} : List α → List α
  | [] => []
  | x :: xs => inversa xs ++ [x]

def inversa' (xs : List α) : List α :=
  match xs with
    | List.nil => List.nil
    | List.cons x xs => inversa' xs ++ [x]


#eval inversa [1, 2, 3, 4, 5]
#eval inversa' [1, 2, 3, 4, 5]


theorem anadir_asociativa (as bs cs : List α) : (as ++ bs) ++ cs = as ++ (bs ++ cs) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    calc
      (a :: as ++ bs) ++ cs
        = a :: (as ++ bs) ++ cs := by rfl
      _ = a :: (as ++ (bs ++ cs)) := by simp [ih]
      _ = a :: as ++ (bs ++ cs) := by rfl

theorem inversa_append {α : Type} (xs ys : List α) : inversa (xs ++ ys) = inversa ys ++ inversa xs := by
  induction xs with
  | nil => simp [inversa]
  | cons x xs ih =>
    calc
      inversa (x :: xs ++ ys)
        = inversa (xs ++ ys) ++ [x] := by simp [inversa]
      _ = inversa ys ++ inversa xs ++ [x] := by rw [ih]
      _ = inversa ys ++ (inversa xs ++ [x]) := by rw [anadir_asociativa]

theorem inversa_inversa {α : Type} (xs : List α) : inversa (inversa xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    calc
      inversa (inversa (x :: xs))
        = inversa (inversa xs ++ [x])         := by simp [inversa]
      _ = inversa [x] ++ inversa (inversa xs) := by rw [inversa_append] -- inversa (xs = (inversa xs) ++ ys = ([x]))
      _ = inversa [x] ++ xs                   := by rw [ih]
      _ = [x] ++ xs                           := by simp [inversa]
      _ = x :: xs                             := by rfl

