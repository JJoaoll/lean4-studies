structure Pos where
  succ ::
  pred : Nat
--deriving Repr

-- Define instances of
-- Add,
-- Mul,
-- ToString,
-- and OfNat
-- that allow this version of Pos to be used conveniently.

open Pos
def addPos : Pos → Pos → Pos
  | succ 0      , succ m => succ (Nat.succ m)
  | succ (n + 1), succ m => addPos (succ n) (succ $ Nat.succ m)

instance : Add Pos where
  add := addPos

def three := succ 2

#eval three
#eval addPos (succ 0) (succ 4)
#eval addPos three three


def mulPos : Pos → Pos → Pos
  | succ 0      , p => p
  | succ (n + 1), p => p + mulPos (succ n) p

instance : Mul Pos where
  mul := mulPos

#eval three
#eval three + three
-- #eval three × three --> error
#eval three * three

-- ToString,
-- and OfNat

def posToString (parenOpt : Bool) (p : Pos) : String :=
  let succString s := if parenOpt then "succ (" ++ s ++ ")" else "succ " ++ s
  match p with
  | succ 0       => "one"
  | succ (n + 1) => succ n |> posToString parenOpt |> succString

#eval posToString false three

instance : ToString Pos where
  toString := posToString false

#eval three

instance : OfNat Pos (n + 1) where
  ofNat := succ n
    -- let rec natPlusOne : Nat → Pos
    --   | 0     => succ 0
    --   | k + 1 => succ $ k + 1
    -- natPlusOne n

#eval (4 : Pos)
#eval (5 : Pos)
#eval (1 : Pos)
#eval (2 : Pos)
#eval ((2 + 3) : Pos)
#eval ((2 * 3) : Pos)

-- #eval (0 : Pos) --> !Error

-- instance : OfNat Pos (n + 1) where
--   ofNat :=
--     let rec natPlusOne : Nat → Pos
--       | 0 => Pos.one
--       | k + 1 => Pos.succ (natPlusOne k)
--     natPlusOne n

inductive Even where
 | zero : Even
 | next : Even → Even

open Even

def addEven : Even → Even → Even
 | zero  , e' => e' 
 | next e, e' => next $ addEven e e'

instance : Add Even where
  add := addEven

def mulEven : Even → Even → Even
  | zero     , _  => zero
  | next e   , e' => e' + e' + mulEven e e'

instance : Mul Even where
  mul := mulEven

def two := next zero
def four := next two

#eval two
#eval four

#eval two  + four
#eval two  * four 
#eval two  * two
#eval four * four

def evenToString (parenOpt : Bool) (e : Even) : String :=
  let nextStr s := if parenOpt then "next (" ++ s ++ ")" else "next" ++ s
  match e with
  | zero   => "zero"
  | next e => nextStr $ evenToString parenOpt e


def IsEven (n : Nat) : Prop :=
  ∃k : Nat,  2 * k = n

def even : Nat → Bool
 | 0     => true
 | 1     => false
 | n + 2 => even n

theorem even_corretness : ∀n : Nat, IsEven n ↔ even n = true := by
  sorry


-- how to do it ?
-- instance : OfNat evenToString (n) where
--  sorry

#eval posToString false three

instance : ToString Pos where
  toString := posToString false



#check IO.println   --> IO.prinln.{u_1} {α : Type u_1} [ToString α] (s : α) : IO Unit
#check (IO.println) --> IO.println : ?m.10872 → IO Unit
#check @IO.println  --> @IO.println : {α : Type u_1} → [inst : ToString α] → α → IO Unit


def List.summ [Add α] [OfNat α 0] : List α → α
 | []      => 0
 | x :: xs => x + xs.sum

def fourNats : List Nat := [1, 2, 3, 4]

#eval fourNats.summ

-- inductive BinTree α where
--  | tip  : α → BinTree α
--  | node : BinTree α → BinTree α → BinTree α

-- Remembering the past
structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr


instance [Add α] : Add (PPoint α) where
  add p1 p2 := { x := p1.x + p2.x, y := p1.y + p2.y }

#check @OfNat.ofNat
#check @Add.add

#check PPoint

instance [Mul α] : HMul (PPoint α) α (PPoint α) where
  hMul := fun p aₛ => PPoint.mk (p.x * aₛ) (p.y * aₛ)

instance [Mul α] : HMul α (PPoint α) (PPoint α) where
  hMul := fun aₛ p => PPoint.mk (p.x * aₛ) (p.y * aₛ)

#eval {x := 2.5, y := 3.7 : PPoint Float} * 2.0

#check "oi"
#check String
#check Type
