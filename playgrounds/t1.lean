/- Define some constants. -/

def m : Nat := 1       -- m is a natural number
def n : Nat := 0
def b1 : Bool := true  -- b1 is a Boolean
def b2 : Bool := false

/- Check their types. -/

#check m            -- output: Nat
#check n
#check n + 0        -- Nat
#check m * (n + 0)  -- Nat
#check b1           -- Bool
#check b1 && b2     -- "&&" is the Boolean and
#check b1 || b2     -- Boolean or
#check true         -- Boolean "true"

/- Evaluate -/

#eval 5 * 4         -- 20
#eval m + 2         -- 3
#eval b1 && b2      -- false

#check Nat               -- Type
#check Bool              -- Type
#check Nat → Bool        -- Type
#check Nat × Bool        -- Type
#check Nat → Nat         -- ...
#check Nat × Nat → Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check Nat → Nat → Bool
#check (Nat → Nat) → Nat

def α : Type := Nat
def β : Type := Bool
def G : Type → Type → Type := Prod

#check α        -- Type
#check G α      -- Type → Type
#check G α β    -- Type
#check G α Nat  -- Type


#check Prod α β       -- Type
#check α × β          -- Type

#check Prod Nat Nat   -- Type
#check Nat × Nat      -- Type
#check Type     -- Type 1
#check Type 1   -- Type 2
#check Type 2   -- Type 3
#check Type 3   -- Type 4
#check Type 4   -- Type 5

#check Prop
#check trivial

#check List    -- List.{u} (α : Type u) : Type u
#check Prod    -- Prod.{u, v} (α : Type u) (β : Type v) : Type (max u v)

def F'.{u} (α : Type u) : Type u := Prod α α

def F (α : Type u) : Type u := Prod α α


#check F    -- Type u → Type u

variable (x y : Nat)
variable (n : true)

def compose (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

variable (α β γ : Type)
def doTwice (h : α → α) (x : α) : α :=
  h (h x)

def doThrice (h : a → a) (x : a) : a :=
  h (h (h x))

#check Sigma.mk 3 4
#check (3, 4)


#check doThrice
#eval doThrice (· + 1) 3

-- def brincador (b : True) : Nat := 5

universe u v

def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a :=
  ⟨a, b⟩

def g (α : Type u) (β : α → Type v) (a : α) (b : β a) : Σ a : α, β a :=
  Sigma.mk a b

def h0 (n : Nat) : List Nat :=
  (f Type List Nat [n]).2

def h02 (n : Nat) : Type :=
  (f Type List Nat [n]).1

#check h0
#check h0 3
#eval  h0 3

def h1 (x : Nat) : Nat :=
  (f Type (fun α => α) Nat x).2

#eval h1 5 -- 5

def h2 (x : Nat) : Nat :=
  (g Type (fun α => α) Nat x).2

#eval h2 5 -- 5

section
  variable {α : Type u}
  variable (x : α)
  def ident := x
end

#check ident
#check ident 4
#check ident "hello"

#check id 3      --> Nat
#check @id Int 3 --> Int

#check "olamundo"
#check (4 : Int)
#check String
#check Int
#check Type

open List

-- def sum : List Int → Int
--   := foldl (· + ·) 0

-- def subsequences {α : Type} : List α → List (List α)
--   | [] => [[]]
--   | a :: as =>
--     let ass := subsequences as
--     ass.map (a :: ·) ++ ass

-- version com max?
def bigger := foldl max (0 : Int)

def tails {α : Type} (as : List α) : List (List α) :=
  match as with
  | [] => [[]]
  | _ :: as' => as :: tails as'

#eval tails [1, 2, 3]

def inits {α : Type} (as : List α) : List (List α) :=
  match as with
  | [] => []
  | a :: as' => [a] :: (cons a <$> inits as')

#eval inits [1, 2, 3]
#eval inits [1, 2]
#eval inits [3]

#eval tails [1, 2, 3]
#eval tails [1, 2]
#eval tails [3]

def subsequences {α : Type} : List α → List (List α) :=
  flatten ∘ map inits ∘ tails


#eval flatten (map inits $ tails [1, 2, 3] )
def solution :=
  bigger ∘ map sum ∘ subsequences

#eval solution [-1, -4, 3, -2, 44, -40, 8, 9, 11, 10, 0, 0, -1]
#eval solution [3, -2, 44, -40, 8, 9, 11, 10]

#eval subsequences [1, 2, 3]
#eval subsequences [1, 2]

#eval sum [1, -4, 5, 8, -1, 9]
#eval sum [-4 -1]
#eval sum ([] : List Int)
#eval sum [5, 8, -1]
#eval sum [5, 8]
#eval sum [1, -4, 5, 8]
#eval sum [5, 8, -1, 9]
