import  ff

def Tuple (α : Type) (n : Nat) :=
  { as : List α // as.length = n }

-- notation something "_" => ⟨something, by decide⟩
#check (["oi", "tchau", "hello", "bye"] _ : Tuple String 4)

def f {n : Nat} (t : Tuple α n) : Nat := by
  cases n; exact 3; exact 7

def myTuple : Tuple Nat 3 := [0, 1, 2] _
  -- ⟨[0, 1, 2], rfl⟩

example : f myTuple = 7 :=
  rfl

inductive Foo where
  | bar1 : Nat → Nat → Foo
  | bar2 : Nat → Nat → Nat → Foo

def silly (x : Foo) : Nat := by
  cases x with
  | bar1 a b => exact b
  | bar2 c d e => exact e

open Nat

example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (succ n)) (m k : Nat)
        : p (m + 3 * k) := by

  cases m + 3 * k
  exact hz   -- goal is p 0
  apply hs   -- goal is a : Nat ⊢ p (succ a)

-- the same
example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (succ n)) (m k : Nat)
        : p (m + 3 * k) := by
  generalize m + 3 * k = n
  cases n
  exact hz   -- goal is p 0
  apply hs   -- goal is a : Nat ⊢ p (succ a)

#check "oi"
#check String
#check Type
example (p : Prop) (m n : Nat)
        (h₁ : m < n → p) (h₂ : m ≥ n → p) : p := by
  cases Nat.lt_or_ge m n
  case inl hlt => exact h₁ hlt
  case inr hge => exact h₂ hge




def even (n : Nat) : Prop := 2 ∣ n

#check even

#print Subtype

#check {n : Nat // n > 2 ∧ even n}

notation type "<" n => {x : type // x < n}

structure RGB where
  red   : Nat<256
  green : Nat<256
  blue  : Nat<256
-- deriving Repr

notation n "_" => ⟨n, by decide⟩

instance : ToString RGB where
  toString
    | ⟨⟨x, _⟩, ⟨y, _⟩, ⟨z, _⟩⟩  =>
    let sx := toString x
    let sy := toString y
    let sz := toString z
    s!"RGB: ({sx}, {sy}, {sz})"


def test : RGB := ⟨4 _, 4 _, 23 _⟩

#eval test
def fail : RGB := ⟨400 _, 400 _, 23213213 _⟩
