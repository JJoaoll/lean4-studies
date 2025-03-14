inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos

def Pos.plus : Pos → Pos → Pos
  | Pos.one, k => Pos.succ k
  | Pos.succ n, k => Pos.succ (n.plus k)

def seven : Pos :=
  Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one)))))

instance : Add Pos where
  add := Pos.plus

def fourteen : Pos := seven + seven

def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1

instance : ToString Pos where
  toString x := toString (x.toNat)

#eval s!"There are {seven}"

def Pos.mul : Pos → Pos → Pos
  | Pos.one, k => k
  | Pos.succ n, k => n.mul k + k

instance : Mul Pos where
  mul := Pos.mul

#eval [seven * Pos.one,
       seven * seven,
       Pos.succ Pos.one * seven]

def NatList (α : Type) : Nat → Type
  | 0     => α
  | n + 1 => List $ NatList α n

def test {α : Type} (a : α) (n : Nat) : NatList α n :=
  match n with
  | 0     => a
  | _ + 1 => []

#eval  test 42 5
#check test 42 5

inductive LT4 where
  | zero
  | one
  | two
  | three
deriving Repr

instance : OfNat LT4 0 where
  ofNat := LT4.zero

instance : OfNat LT4 1 where
  ofNat := LT4.one

instance : OfNat LT4 2 where
  ofNat := LT4.two

instance : OfNat LT4 3 where
  ofNat := LT4.three

#eval (3 : LT4)
#eval (0 : LT4)

-- #eval (4 : LT4) --> !Error
-- Gambiarra?!
instance : OfNat Pos (n + 1) where
  ofNat :=
    let rec natPlusOne : Nat → Pos
      | 0 => Pos.one
      | k + 1 => Pos.succ (natPlusOne k)
    natPlusOne n


def eight : Pos := 8
#eval eight
#eval (8 : Pos)
-- #eval (0 : Pos) --> !Error
-- def zero : Pos := 0 --> !Error

def addNatPos : Nat → Pos → Pos
  | 0, p => p
  | n + 1, p => Pos.succ (addNatPos n p)

def addPosNat : Pos → Nat → Pos
  | p, 0 => p
  | p, n + 1 => Pos.succ (addPosNat p n)


instance : HAdd Nat Pos Pos where
  hAdd := addNatPos

instance : HAdd Pos Nat Pos where
  hAdd := addPosNat

#eval  (3 : Pos) + (5 : Nat) --> 8
#eval  (3 : Nat) + (5 : Pos) --> 8

#check (3 : Pos) + (5 : Nat) -->  8
#check (3 : Nat) + (5 : Pos) --> 8

class HPlus (α : Type) (β : Type) (γ : outParam Type) where
  hPlus : α → β → γ

instance : HPlus Nat Pos Pos where
  hPlus := addNatPos

instance : HPlus Pos Nat Pos where
  hPlus := addPosNat

instance : HPlus Pos Nat String where
  hPlus := fun _ _ => "oi"

#eval HPlus.hPlus  (3 : Pos) (5 : Nat)
#check HPlus.hPlus (3 : Pos) (5 : Nat)
#check HPlus.hPlus (3 : Pos) (5 : Nat)

instance [Add α] : HPlus α α α where
  hPlus := Add.add

#eval HPlus.hPlus (3 : Nat) (5 : Nat)
#check HPlus.hPlus (5 : Nat) (3 : Nat)
#check HPlus.hPlus (5 : Nat)
