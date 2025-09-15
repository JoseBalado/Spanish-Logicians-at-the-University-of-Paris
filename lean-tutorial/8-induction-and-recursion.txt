-- https://leanprover.github.io/theorem_proving_in_lean4/induction_and_recursion.html#well-founded-recursion-and-induction
-- Fix takeWhile
-- Lean 4: takeWhile for Arrays
-- Mimics the behavior of takeWhile in functional languages.

def takeWhile (p : α → Bool) (as : Array α) : Array α :=
  go 0 #[]
where
  go (i : Nat) (r : Array α) : Array α :=
    if h : i < as.size then
      let a := as[i]  -- Safe indexed access
      if p a then
        go (i + 1) (r.push a)
      else
        r
    else
      r
  termination_by as.size - i  -- Prove recursion terminates

-- Example usage
#eval takeWhile (fun x => x < 3) #[1, 2, 3, 4, 5]
-- Expected: #[1, 2]


-- Goal
--- Take elements from the start of an array as long as they satisfy a predicate.

-- Step-by-Step Execution

takeWhile (fun x => x < 3) #[1, 2, 3, 4, 5]


--- Call go 0 #[]
--- Start with index i = 0 and empty result array #[].

--- First iteration (i = 0)
    Element: as[0] = 1
    Predicate: 1 < 3 → true
    Add 1 to result.
    Recurse: go 1 #[1]

--- Second iteration (i = 1)
    Element: as[1] = 2
    Predicate: 2 < 3 → true
    Add 2 to result.
    Recurse: go 2 #[1, 2]

--- Third iteration (i = 2)
    Element: as[2] = 3
    Predicate: 3 < 3 → false
    Predicate fails → return current result: #[1, 2]


--- How the where Clause Works
--- In Lean 4, the where clause lets you define local helper functions.
--- Even though go is defined after it’s called (go 0 #[]), Lean allows this because where scopes the function locally.
--- It’s equivalent to defining go inside takeWhile as a let rec.



-- Why Use termination_by?
--- Lean 4 requires recursive functions to prove they terminate.
    termination_by as.size - i

--- This tells Lean that with every recursive call:
    i increases
    as.size - i decreases
    Eventually, i >= as.size and recursion stops


-- Final Output
#eval takeWhile (fun x => x < 3) #[1, 2, 3, 4, 5]
-- Output: #[1, 2]
-- The function stops at 3 because it no longer satisfies the predicate.



----------------------------------------------------------------------------------------------------------------
-- https://leanprover.github.io/theorem_proving_in_lean4/induction_and_recursion.html#mutual-recursion
theorem even_eq_not_odd2 : ∀ a, even a = not (odd a) := by
  intro a
  induction a
  case zero =>
    simp [even, odd]         -- even 0 = true, odd 0 = false ⇒ true = not false
  case succ a ih =>
    simp [even, odd, ih]     -- unfolds definitions and uses induction hypothesis

/-
- **Proof**:
  - The proof uses induction on `a`:
    1. **Base Case** (`a = 0`): 
       - For `a = 0`, `even 0 = true` and `odd 0 = false`. The goal simplifies to `true = not false`, which is true. The `simp` tactic handles this simplification.
    2. **Inductive Step**:
       - Assume the theorem holds for `a` (inductive hypothesis). Prove it for `a + 1`.
       - Using the definitions of `even` and `odd`, the goal simplifies to `odd a = not (even a)`, which follows directly from the inductive hypothesis. The `simp` tactic, combined with the `*` wildcard to apply the inductive hypothesis, completes the proof.

### Summary:
This code defines mutually recursive functions to determine evenness and oddness, demonstrates their behavior with examples, and proves a fundamental property (`even_eq_not_odd`) about their relationship. The use of mutual recursion and induction highlights Lean's ability to handle interdependent definitions and proofs effectively.
-/


theorem even_eq_not_odd3 : ∀ a, even a = not (odd a) := by
  intro a
  induction a
  case zero =>
      calc
        even 0
          = true := rfl                   -- by definition of even
        _ = not false := by rfl           -- true = not false
        _ = not (odd 0) := by rw [odd]    -- odd 0 = false
  case succ a ih =>
    simp [even, odd, ih]     -- unfolds definitions and uses induction hypothesis


----------------------------------------------------------------------------------------------------------------------
mutual
  inductive Even : Nat → Prop where
    | even_zero : Even 0
    | even_succ : ∀ n, Odd n → Even (n + 1)

  inductive Odd : Nat → Prop where
    | odd_succ : ∀ n, Even n → Odd (n + 1)
end

/-
# What does Nat → Prop mean?
This is a function type in Lean. It means:
    A function that takes a Nat (natural number) and returns a Prop (proposition).

In other words:
    Even : Nat → Prop

Means:
"Even is a function that, given a natural number n, gives you a proposition — specifically, the proposition that n is even."


# What is Prop?
In Lean:
    Type is the universe of computational data — like numbers, lists, trees, etc.
    Prop is the universe of logical propositions — things that are either true or false.

So:
    Nat is a type: the type of natural numbers.
    Even n : Prop is a proposition — it asserts that n is even.

# What is Even 0?
When we write:
    Even 0

We're applying the function Even : Nat → Prop to the argument 0, so:
    Even 0 : Prop

This means:
    "The proposition that 0 is even."

And the constructor:
    Even.even_zero : Even 0

is a proof of that proposition. That is, Even.even_zero is a term whose type is Even 0, meaning it proves that 0 is even.


# So how do Even and Even 0 relate?
    Even is a function from Nat to Prop.
    Even 0 is a specific proposition (a type in Prop).
    Even.even_zero is a proof (a value that inhabits the type Even 0).

This follows the Curry–Howard correspondence, which says:
    Types are Propositions, and Values are Proofs.

So in this case:
    Concept	        In Lean	                Meaning
    Proposition	    Even 0	                "0 is even"
    Proof	        Even.even_zero	        Proof that 0 is even
    Function	    Even : Nat → Prop	    Function that gives "n is even"

# Want a real-world analogy?
Think of Even like a mathematical property:
    Saying "Even 4" is like saying "4 is even."
    Saying "Even is a function Nat → Prop" is like saying: "For each number, we can ask: 'Is it even?' — and the answer is a proposition."

-/




theorem not_odd_zero : ¬ Odd 0 :=
  fun h => nomatch h

/-
# What does this mean?
¬ Odd 0 is read as:
    "It is not the case that 0 is odd"
or simply,
    "0 is not odd"

We're proving this by contradiction. That is:
    Suppose someone claims Odd 0 holds — then we show this leads to a contradiction.


# Let's look at the proof:
    fun h => nomatch h

This is:
    A function taking an input h : Odd 0
    And saying: "There’s no possible way this input could exist."

The keyword nomatch is used in Lean when there are no constructors that match the pattern — meaning, the data type Odd has no way to produce a value for Odd 0.

# Why is that true?
Recall the inductive definition of Odd:
    mutual
      inductive Even : Nat → Prop where
        | even_zero : Even 0
        | even_succ : ∀ n, Odd n → Even (n + 1)

      inductive Odd : Nat → Prop where
        | odd_succ : ∀ n, Even n → Odd (n + 1)
    end

Look at the only constructor for Odd:
    Odd.odd_succ : ∀ n, Even n → Odd (n + 1)

This tells us that:
    Odd numbers are built by adding 1 to an even number.
    So the smallest number for which Odd can be constructed is 1 (which is 0 + 1).
    There is no way to construct Odd 0.

    Therefore, Odd 0 has no constructors, and hence no values.


# What does nomatch h do?
Lean uses nomatch to signal that the value h cannot match any constructor of the inductive type (here, Odd 0 has no constructors).
This tells Lean:
    “We assumed h : Odd 0, but Odd 0 is uninhabited — contradiction!”

# In plain English
To prove that 0 is not odd, suppose it is. But by the definition of odd numbers, there's no way to construct a proof of Odd 0. Therefore, such a proof cannot exist — contradiction.
-/


-- More examples:
def even_0 : Even 0 := even_zero
def odd_1  : Odd 1   := odd_succ 0 even_0
def even_2 : Even 2 := even_succ 1 odd_1
def odd_3  : Odd 3   := odd_succ 2 even_2
def even_4 : Even 4 := even_succ 3 odd_3
def odd_5  : Odd 5   := odd_succ 4 even_4


def even0 : Even 0 := even_zero
def odd1  : Odd 1  := odd_succ 0 even_zero
def even2 : Even 2 := even_succ 1 (odd_succ 0 even_zero)
def odd3  : Odd 3  := odd_succ 2 (even_succ 1 (odd_succ 0 even_zero))
def even4 : Even 4 := even_succ 3 (odd_succ 2 (even_succ 1 (odd_succ 0 even_zero)))
def even5 : Odd 5  := odd_succ 4 (even_succ 3 (odd_succ 2 (even_succ 1 (odd_succ 0 even_zero))))

#check even_0  -- : Even 0
#check odd_1   -- : Odd 1
#check even_2  -- : Even 2
#check odd_3   -- : Odd 3
#check even_4  -- : Even 4



-- Using true or false for the definition of even and false:
mutual
  def isEven : Nat → Bool
    | 0 => true
    | n+1 => isOdd n

  def isOdd : Nat → Bool
    | 0 => false
    | n+1 => isEven n
end

#eval isEven 0  -- true
#eval isOdd 0   -- false
#eval isEven 1  -- false
#eval isOdd 1   -- true
#eval isEven 4  -- true
#eval isOdd 7   -- true




----------------------
/-
For another example, suppose we use a nested inductive type to define a set of terms inductively, so that a term is either a constant (with a name given by a string), or the result of applying a constant to a list of constants.
-/

inductive Term where
| const : String → Term
| app : String → List Term → Term

-- Example terms
-- 1. A simple constant term
-- x
-- This represents a variable or constant in the term language.
-- In this case, we are using a string to represent the name of the constant.
def t1 : Term := Term.const "x"

-- 2. An application of a function to two arguments
-- f(x, y)
def t2 : Term := Term.app "f" [Term.const "x", Term.const "y"]

-- 3. A nested application of functions
-- g(z, f(x, y))
def t3 : Term := Term.app "g" [Term.const "z", Term.app "f" [Term.const "x", Term.const "y"]]

-- Pattern Matching on Term
-- You can use pattern matching to process or evaluate Term values.

open Term
def t4 : Term := const "x"
def t5 : Term := app "f" [const "x", const "y"]
def t6 : Term := app "g" [const "z", app "f" [const "x", const "y"]]


open Term

mutual
-- Helper to convert list of Terms to list of Strings
def termsToStrings : List Term → List String
| [] => []
| t :: ts => termToString t :: termsToStrings ts

-- Main function
def termToString : Term → String
| const s => s
| app f args => f ++ "(" ++ String.intercalate ", " (termsToStrings args) ++ ")"
end

def t7 : Term := const "x"
def t8 : Term := app "f" [const "x", const "y"]
def t9 : Term := app "add" [app "succ" [const "1"], const "2"]

#eval termToString t7 -- "x"
#eval termToString t8 -- "f(x, y)"
#eval termToString t9 -- "add(succ(1), 2)"




/-
As a final example, we define a function replaceConst a b e that replaces a constant a with b in a term e, and then prove the number of constants is the same. Note that, our proof uses mutual recursion (aka induction).
-/

inductive Term where
 | const : String → Term
 | app   : String → List Term → Term
 deriving Repr  -- This enables #eval to work in the examples (needed only in old versions of Lean)

namespace Term
mutual
 def numConsts : Term → Nat
   | const _ => 1
   | app _ cs => numConstsLst cs
  def numConstsLst : List Term → Nat
   | [] => 0
   | c :: cs => numConsts c + numConstsLst cs
end
mutual
  def replaceConst (a b : String) : Term → Term
    | const c => if a == c then const b else const c
    | app f cs => app f (replaceConstLst a b cs)

  def replaceConstLst (a b : String) : List Term → List Term
    | [] => []
    | c :: cs => replaceConst a b c :: replaceConstLst a b cs
end

mutual
  theorem numConsts_replaceConst (a b : String) (e : Term)
            : numConsts (replaceConst a b e) = numConsts e := by
    match e with
    | const c => simp [replaceConst]; split <;> simp [numConsts]
    | app f cs => simp [replaceConst, numConsts, numConsts_replaceConstLst a b cs]

  theorem numConsts_replaceConstLst (a b : String) (es : List Term)
            : numConstsLst (replaceConstLst a b es) = numConstsLst es := by
    match es with
    | [] => simp [replaceConstLst, numConstsLst]
    | c :: cs =>
      simp [replaceConstLst, numConstsLst, numConsts_replaceConst a b c,
            numConsts_replaceConstLst a b cs]
end


-- This replaces all occurrences of constant string a with b, recursively, in a Term.
#eval replaceConst "x" "z" (const "x") -- Term.const "z"
#reduce replaceConst "x" "z" (const "x") -- const "z"

#eval replaceConst "x" "z" (app "f" [const "x", const "y"]) -- Term.app "f" [Term.const "z", Term.const "y"]
#reduce replaceConst "x" "z" (app "f" [const "x", const "y"]) -- app "f" [const "z", const "y"]

-- Example 1: Single constant
-- Both are 1.
#eval numConsts (const "x") -- 1
#eval numConsts (replaceConst "x" "y" (const "x")) -- 1

-- Example 2: Function with multiple constants
-- So x is replaced with z, but the number of constants stays at 3.
def t1 := app "f" [const "x", const "y", const "x"]
#eval numConsts t1 -- 3
#eval numConsts (replaceConst "x" "z" t1) -- 3

-- Example 3: No replacement needed
-- Since "z" wasn't there, nothing changed.
def t2 := app "f" [const "a", const "b"]
#eval numConsts t2 -- 2
#eval numConsts (replaceConst "z" "w" t2) -- 2




------------------------------------------------------------------------------------------------------------------------------
-- https://leanprover.github.io/theorem_proving_in_lean4/induction_and_recursion.html#dependent-pattern-matching

inductive Vector (α : Type u) : Nat → Type u
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
namespace Vector

/-
The Vector Definition
This means:
    - A Vector α n is a list of elements of type α of exact length n.
    - nil represents the empty vector.
    - cons adds one element in front and increases the length by 1.
-/


def tailAux (v : Vector α m) : m = n + 1 → Vector α n :=
  Vector.casesOn (motive := fun x _ => x = n + 1 → Vector α n) v
    (fun h : 0 = n + 1 => Nat.noConfusion h)
    (fun (a : α) (m : Nat) (as : Vector α m) =>
     fun (h : m + 1 = n + 1) =>
       Nat.noConfusion h (fun h1 : m = n => h1 ▸ as))

def tail (v : Vector α (n+1)) : Vector α n :=
  tailAux v rfl
end Vector

/-
Goal: Implement a tail function
We want a function:
    def tail (v : Vector α (n+1)) : Vector α n

That is:
    Input: A vector of length n + 1
    Output: A vector of length n, dropping the first element
    So we remove the head from a non-empty vector.

But we can't just pattern-match blindly — because of the dependent type Vector α (n+1), we have to be careful with how we match and ensure all lengths line up.
-/

/-
Step-by-step Explanation of tailAux
Type:
    def tailAux (v : Vector α m) : m = n + 1 → Vector α n

This function says:
    - Give me any vector v of length m
    - And give me a proof that m = n + 1
    - I will return a vector of length n (i.e., drop the head)


Implementation:
    Vector.casesOn (motive := fun x _ => x = n + 1 → Vector α n) v

This says:
    - We destruct v using casesOn
    - The motive is that we want a function from x = n + 1 to Vector α n
    - So depending on the shape of the vector, we’ll produce such a function

Case 1: nil
    (fun h : 0 = n + 1 => Nat.noConfusion h)

    - If the vector is empty (nil), then its length m = 0
    - But we’re being told 0 = n + 1 — impossible!
    - So we use Nat.noConfusion to eliminate this invalid path


Case 2: cons
(fun (a : α) (m : Nat) (as : Vector α m) =>
 fun (h : m + 1 = n + 1) =>
   Nat.noConfusion h (fun h1 : m = n => h1 ▸ as))

This case handles cons a as : Vector α (m + 1):
    - The input 'v' is 'cons a as', where 'as : Vector α m'
    - The proof 'h : m + 1 = n + 1' tells us that the tail length m must equal n
    - We again use Nat.noConfusion to extract the equality m = n from m + 1 = n + 1
    - Then we use 'h1 ▸ as' to cast 'as : Vector α m' into 'Vector α n'

This is type-safe coercion using equalities.
-/

/-
The Final tail Function:
    def tail (v : Vector α (n+1)) : Vector α n :=
      tailAux v rfl

Now that v is already of length n + 1, we pass the proof rfl : n + 1 = n + 1 to tailAux, and it gives us the tail of type Vector α n.
-/



-----------------------------------------------------------------------------------------------------------
-- https://leanprover.github.io/theorem_proving_in_lean4/induction_and_recursion.html#inaccessible-patterns

inductive ImageOf {α β : Type u} (f : α → β) : β → Type u where
| imf : (a : α) → ImageOf f (f a)

open ImageOf

def inverse {f : α → β} : (b : β) → ImageOf f b → α
| .(f a), imf a => a

def double (n : Nat) : Nat := n * 2

#check ImageOf double 4
/-
This is asking:
Is there a value a : Nat such that double a = 4?

Yes! That value is 2, because double 2 = 4.

So, you can construct a proof:
```
def fourIsInTheImageOfDouble : ImageOf double 4 := imf 2
```

This works because:
2 : Nat
double 2 = 4
Therefore imf 2 : ImageOf double 4

```
imf 2 : ImageOf double 4
```

means:
a = 2
f = double
f a = 4
So ImageOf double 4 holds, and imf 2 is the proof.
-/


def fourIsInTheImageOfDouble : ImageOf double 4 := imf 2
/-
(f a) is in the image of f because there exists an a such that f a = b."
So the type ImageOf f b means “b is in the image of f”,
and the constructor imf a is the witness that b = f a.
-/

/-
Substitution in ImageOf
Let's break down what gets substituted when you write imf 2 in this context:

ImageOf double 4
-- expects a proof that some a exists such that double a = 4

imf 2
-- produces a value of type ImageOf double (double 2) = ImageOf double 4

So:
a = 2
f = double
f a = double 2 = 4
Therefore, imf 2 : ImageOf double 4

The values are substituted like this:

ImageOf f (f a)
⟶ ImageOf double (double 2)
⟶ ImageOf double 4
-/


#eval inverse 4 fourIsInTheImageOfDouble
def inverseDouble4 : (inverse 4 fourIsInTheImageOfDouble) = 2 := rfl
/-
```
def inverse {f : α → β} : (b : β) → ImageOf f b → α
| .(f a), imf a => a
```

This says:
"If you know that b = f a and you have a proof of that (imf a), then you can get a back."

So:
inverse 4 fourIsInTheImageOfDouble
-- → 2

You can even prove it:
```
def inverseDouble4 : inverse 4 fourIsInTheImageOfDouble = 2 := rfl
```

Because inverse 4 (imf 2) unfolds directly to 2.
-/

/-
def inverse {f : α → β} : (b : β) → ImageOf f b → α
| .(f a), imf a => a


So, inverse is a function that:
Takes a value b : β
And a proof that b = f a, encoded as imf a : ImageOf f (f a)
which is:
(fourIsInTheImageOfDouble : ImageOf double 4 := imf 2)
And returns the 'a' such that f a = b

What are the actual arguments:
.(f a) matches 4, because 4 = double 2
b = 4
imf a = imf 2
a = 2
f = double

-/




namespace Hidden
inductive Vector (α : Type u) : Nat → Type u
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)

namespace Vector

def add [Add α] : {n : Nat} → Vector α n → Vector α n → Vector α n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (a + b) (add as bs)

-- Optional: A helper function to convert Vector to List for pretty printing
def toList : {n : Nat} → Vector Nat n → List Nat
  | 0, nil => []
  | n+1, cons a as => a :: toList as

def v1 : Vector Nat 3 :=
  cons 1 (cons 2 (cons 3 nil))

def v2 : Vector Nat 3 :=
  cons 4 (cons 5 (cons 6 nil))

def v3 : Vector Nat 3 := add v1 v2  -- element-wise addition


#eval toList v3  -- Output should be [5, 7, 9]
#eval v3

end Vector
end Hidden




--------------------------------------------------------------------------------------------------
-- https://leanprover.github.io/theorem_proving_in_lean4/induction_and_recursion.html#match-expressions

variable (p q : Nat → Prop)

example : (∃ x, p x) → (∃ y, q y) → ∃ x y, p x ∧ q y
  | ⟨x, px⟩, ⟨y, qy⟩ => ⟨x, y, px, qy⟩

/-
This Lean code defines a theorem (without naming it, using `example`) that proves a logical statement about existential quantifiers. The theorem shows that if there exists some `x` that satisfies property `p`, and there exists some `y` that satisfies property `q`, then there exist values `x` and `y` such that both `p x` and `q y` are true simultaneously.

The proof is written using pattern matching on the structure of the existential proofs:
- `(∃ x, p x) → (∃ y, q y) → ∃ x y, p x ∧ q y` is the theorem statement.
- The pattern `| ⟨x, px⟩, ⟨y, qy⟩ =>` destructures the proof of the two existential statements:
  - `⟨x, px⟩` is the first assumption, representing a value `x` and a proof `px` that `p x` holds.
  - `⟨y, qy⟩` is the second assumption, representing a value `y` and a proof `qy` that `q y` holds.
- The expression `⟨x, y, px, qy⟩` constructs the proof of the conclusion `∃ x y, p x ∧ q y`, providing:
  - The witness `x` from the first assumption
  - The witness `y` from the second assumption
  - The proof `px` that `p x` holds
  - The proof `qy` that `q y` holds

This proof demonstrates how to combine existential proofs to form a new existential statement with a conjunction. It shows that if properties `p` and `q` are each satisfied by some value, then there exist values that satisfy both properties simultaneously.

-/


-- Defining variable p and q in a different way
-- to show that the proof is still valid.


def p x := x = 1
def q (y : Nat) := y = 2
def r (y : Nat) : Prop := y = 2
variable (t : Nat → Prop)

#check p -- p (x : Nat) : Prop
#check p 1 -- p 1 : Prop
#check p 2 -- p 2 : Prop
#check t -- t : Nat → Prop

example : (∃ x, p x) → (∃ y, q y) → ∃ x y, p x ∧ q y
  | ⟨x, px⟩, ⟨y, qy⟩ => ⟨x, y, px, qy⟩


-- To be able to use #eval with p x use DecidablePred:
/-
#eval p 1
failed to synthesize
  Decidable (p 1)
-/

def p x := x = 1
instance : DecidablePred p := fun x => inferInstanceAs (Decidable (x = 1))

#eval p 1
#eval p 2




----------------------------------------------------------------------------------------------------
-- https://leanprover.github.io/theorem_proving_in_lean4/induction_and_recursion.html#local-recursive-declarations-1

-- Fix problem with:
-- tactic 'simp' failed, nested error:
-- maximum recursion depth has been reached

def replicate (n : Nat) (a : α) : List α :=
 let rec loop : Nat → List α → List α
   | 0,   as => as
   | n+1, as => loop n (a::as)
 loop n []

theorem length_replicate (n : Nat) (a : α) : (replicate n a).length = n := by
  let rec aux (n : Nat) (as : List α)
              : (replicate.loop a n as).length = n + as.length := by
    match n with
    | 0   => simp [replicate.loop]
    | n+1 => simp only [replicate.loop, Nat.add_succ, Nat.succ_add]; exact aux n (a :: as) -- <----------------
  exact aux n []

#eval replicate 5 "a"

