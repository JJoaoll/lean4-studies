#check List

#check "oi"

section monad
#print Option

def opt_four : Option Nat
  := some 4

def opt_five: Option Nat
  := none

#eval some 4

#eval (none : Option Nat)
#check some 4
#check (none : Option Nat)

#eval opt_four.map (· + 1)
#eval opt_four.map (· + 4)
#eval opt_five.map (· + 4)

-- interface monad:
-- pure/return : α → m α
-- bind        : m α × (α → m β) → m β

#eval (pure 4 : Option Nat)

def pred (n : Nat) : Option Nat :=
  if n = 0 then
    none
  else
    some (n - 1)

def div2 (n : Nat) : Option Nat :=
  if n % 2 = 0 then
    some (n / 2)
  else
    none

#eval pred 4
#eval pred 5
#eval pred 0

#eval div2 4
#eval div2 12
#eval div2 33

def rust (n : Nat) : IO (Option Nat) := do {
  let opt_x ← pure $ div2 n
  match opt_x with
  | none     => return none
  | some val =>
    let opt_y ← pure $ div2 val
    match opt_y with
    | none     => return none
    | some val =>
      let opt_z ← pure $ div2 val
      return opt_z
}

def ffor (i : Nat) (process : Nat → IO α) : IO Unit := do
  match i with
  | 0     => return ()
  | k + 1 =>
    let _ ← process k
    ffor k process


#check ()
def imperative : IO Unit := do
  let opt_x ← rust 4
  let opt_x ← rust 8
  let opt_x ← rust 8
  let opt_x ← rust 8
  let opt_x ← rust 48

  return ()

#eval rust 48

-- interface monad:
-- pure/return : α → m α
-- bind        : m α × (α → m β) → m β

#eval div2 48
#eval bind (some 48) div2
#eval bind (div2 48) div2
#eval bind (bind (div2 48) div2) div2

#eval div2 48 >>= div2
              >>= div2

#eval some 48 >>= div2
              >>= div2
              >>= pure ∘ (· + 2)
              >>= div2

#eval do {
  let x ← div2 48
  let y ← div2 x
  let z ← div2 (y + 2)

  return z
}



end monad



def l := [1, 2, 3, 4]
#check (· = ·)

def double (n : Nat) : Nat :=
  match n with
  | 0     => 0
  | k + 1 => 2 + double k

#eval double 4

-- > double 4
-- > if 4 = 0 then 0 else 2 + double (4 - 1)
-- > 2 + double (4 - 1)
-- > 2 + double (3)
-- > 2 + double (3)
-- > 2 + (2 + double 2)
-- > 2 + (2 + (2 + double 1))
-- > 2 + (2 + (2 + (2 + double 0)))
-- > 2 + (2 + (2 + (2 + 0)))
-- > 8

-- def pow (n : Nat) (l : List Type) (p : l.length = n):=
--   match n with
--   | 0 => Unit
--   | 1 => α
--   | k + 1 => α × (pow k α)

-- def curry (n : Nat) (f : pow n α → ) :=
--   match n with
--   | 0 =>
--   o

inductive MyNat where
| O : MyNat
| S : MyNat → MyNat

class Semigroup (s : Type) where
  op : s × s → s

def curry : (α × β → γ) → (α → β → γ) :=
  fun f a b => f (a, b)

def three (_ : Nat × Nat × Nat) : Nat := 4
def test (_ : Nat × Nat × Nat × Nat × Nat × Nat) : Nat := 4

def three2 (_ : (Nat × Nat) × Nat) : Nat := 5

#check (curry ∘ curry) three2

#check fun x => curry ((curry test) x)
#check ((curry ∘ ·) ∘ curry) test
#check (((curry ∘ ·) ∘ ·) ∘ ((curry ∘ ·) ∘ curry)) test
#check fun x => (curry ∘ (curry test)) x
#check fun y => fun x => curry (curry ((curry test) x) y )
#check curry test
#check curry ∘ (curry test)
#check fun x => (curry ∘ (curry test))
#check fun y => fun x => curry ((curry (curry test)))
#check curry ∘ curry test
#check curry
#check fun x => curry ((curry test) x)
#check fun x => curry ((curry test) x)
#check (curry ∘ ·) ∘ (curry ∘ (curry test))
#check fun y => fun x => curry $ (curry $ (curry test) x) y
#check fun y => fun x => curry $ (curry $ (curry test) x) y
#check ((curry ∘ ·) ∘ ·) ∘ ((curry ∘ ·) ∘ (curry ∘ (curry test)))
#check (((curry ∘ ·) ∘ ·) ∘ ·) ∘ ((curry ∘ ·) ∘ ·) ∘ ((curry ∘ ·) ∘ (curry ∘ (curry test)))
#check (curry ∘ curry ∘ curry) test
#check (curry ∘ curry) ∘ (curry ∘ curry) test

#check
-- curry₀ : (f : Unit → β) → β

curry₀ = λf.f()
curry₁ = id
curry₂ = curry™
curryₙ = λxₙ.curry™ ∘ (curryₙ₋₁ x)
(f ∘ g) x = f (g x)

1 = curry test
2 = (curry (1))
3 = (curry ∘) ∘ (2)
4 = (curry ∘) ∘) ∘ (3)
5 = ((((curry ∘) ∘) ∘) ∘ (4)


1 = curry test
2 = λx.curry ((1) ∘  x))
3 = λy.λx.curry ((2) ∘ y))
4 = λz.λy.λ.x.curry ((3) ∘ z))
4 = λa.λz.λy.λ.x.curry ((4) ∘ a))

curry₃  = λx₃. curry™ (curry₂ x₃)
        = λx₃. curry™ (curry™ x₃)
        = λx₃. (curry™ ∘ curry™) x₃
        = (curry™ ∘ curry™).

curry₄ = λx₄. curry™ (curry₃ x₄)
       = λx₄. (curry™ ∘ curry₃) x₄
       = (curry™ ∘ curry₃)
       = (curry™ ∘ (curry™ ∘ curry™))

curry₀ = λf.f()
curry₁ = id
curry₂ = curry™
curryₙ = λxₙ.curry™ ∘ (curryₙ₋₁ x)

curry₃  = λx₃. curry™ ∘ (curry₂ x₃)
        = λx₃. ((curry™ ∘) curry™) x₃
        = (curry™ ∘) curry™ parentese eh optional...
