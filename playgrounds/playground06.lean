
inductive BinTree α where
| leaf   : α → BinTree α
| branch : BinTree α → BinTree α → BinTree α

open BinTree

def BinTreeToString [ToString α ] (t : BinTree α) : String :=
  let format (c : String) (str : String) : String := s!"{c}: ({str})"
  match t with
  | leaf x     => toString x
  | branch l r => format "L" (BinTreeToString l) ++ " " ++
                  format "R" (BinTreeToString r)

instance [ToString α] : ToString (BinTree α) where
  toString := BinTreeToString

#eval 3
#eval leaf "oi"
#eval leaf 42
#eval branch (leaf 33) (leaf 32)

class Funktor (F : Type → Type) where
  -- Operations:
  map : {α β : Type} → (α → β) → F α → F β

  mapConst {α β : Type} (x : α) (coll : F β) : F α :=
    map (fun _ => x) coll

  -- Laws:
  -- id_law   : ∀(f_a : F α), map id f_a = fa
  -- comp_law : ∀(f : α → β), ∀(g : β → γ), ∀(f_a : F α),
  --              map (g ∘ f) f_a = map g (map f f_a)

  -- Being associative was a theorem then?

def binTreeMap : (α → β) → (BinTree α → BinTree β)
  | f, leaf x     => leaf (f x)
  | f, branch l r => branch (binTreeMap f l) (binTreeMap f r)

instance : Funktor BinTree where
  map := binTreeMap

inductive Pos where
| one  : Pos
| succ : Pos → Pos

-- i'll redo this to fix the let rec in my mind.
-- def Pos.toNat : Pos → Nat
--   | Pos.one    => 1
--   | Pos.succ n => n.toNat + 1

-- -- #eval [1, 2, 3, 4].drop (2 : Pos) --> error

-- instance : Coe Pos Nat where
--   coe x := x.toNat

-- just for use the let thing..
instance : Coe Pos Nat where
  coe :=
    let rec Pos.toNat : Pos → Nat
      | Pos.one => 1
      | Pos.succ p => Pos.toNat p + 1
    Pos.toNat

instance : OfNat Pos (n + 1) where
  ofNat :=
    let rec natPlusOne : Nat → Pos
      | 0     => Pos.one
      | k + 1 => Pos.succ $ natPlusOne k
    natPlusOne n

#eval  [1, 2, 3, 4].drop ((Pos.succ Pos.one) : Pos)
#check [1, 2, 3, 4].drop (Pos.one.succ)
#check [1, 2, 3, 4].drop (2 : Pos)
#eval  [1, 2, 3, 4].drop (2 : Pos)

def oneInt : Int := Pos.one
#check oneInt

inductive A where
  | a

inductive B where
  | b

instance : Coe A B where
  coe _ := B.b

instance : Coe B A where
  coe _ := A.a

instance : Coe Unit A where
  coe _ := A.a

def coercedToB : B := ()
#eval coercedToB

def List.last? : List α → Option α
  | [] => none
  | [x] => x
  | _ :: x :: xs => last? (x :: xs)

#check ("oi" : Option String)
#check Option Type
def perhapsPerhapsPerhaps : Option (Option (Option String)) :=
  "Please don't tell me"
 def perhapsPerhapsPerhapsNat : Option (Option (Option Nat)) :=
  ↑(392 : Nat)


def isEven (n : Nat) := ∃(k : Nat), 2 * k = n

structure User where
  id     : Int
  name   : String
  salary : Float
deriving Repr

#eval User.mk 1 "Joao" 3000.0

structure NonEmptyList (α : Type) where
  head : α
  tail : List α

instance : Coe (NonEmptyList α) (List α) where
  coe
    | { head := x, tail := xs } => x :: xs

instance : CoeDep (List α) (x :: xs) (NonEmptyList α) where
  coe := {head := x, tail := xs}

structure Monoid where
  Carrier : Type
  neutral : Carrier
  op : Carrier → Carrier → Carrier

def natMulMonoid : Monoid :=
  { Carrier := Nat, neutral := 1, op := (· * ·) }

def natAddMonoid : Monoid :=
  { Carrier := Nat, neutral := 0, op := (· + ·) }

def stringMonoid : Monoid :=
  { Carrier := String, neutral := "", op := String.append }

def listMonoid (α : Type) : Monoid :=
  { Carrier := List α, neutral := [], op := List.append }

#check natMulMonoid
#check natAddMonoid

def foldMap (M : Monoid) (f : α → M.Carrier) (xs : List α) : M.Carrier :=
  let rec go (soFar : M.Carrier) : List α → M.Carrier
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs

#eval foldMap natAddMonoid List.length [[1, 2, 3], [1, 2]]
#eval foldMap natMulMonoid (id : Nat → Nat) [1, 2, 3, 4]


instance : CoeSort Monoid Type where
  coe m := m.Carrier

def ffoldMap (M : Monoid) (f : α → M) (xs : List α) : M :=
  let rec go (soFar : M) : List α → M
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs


#eval ffoldMap natAddMonoid List.length [[1, 2, 3], [1, 2]]
#check Monoid
#check natAddMonoid

-- #check (if · then · else ·) --> !Error & (fun x1 x2 x3 => ?m.9836 : Prop → ?m.9869 → ?m.9869 → ?m.9869)
