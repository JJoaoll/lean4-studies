
inductive BinTreeInt where
  | nil  : BinTreeInt
  | node : Int → BinTreeInt → BinTreeInt → BinTreeInt

open BinTreeInt

def singTree x := node x nil nil

def BinTreeIntToString (t : BinTreeInt) : String :=
  match t with
  | nil              => ""
  | node val nil nil => s!"node {val}"
  | node val l nil   => s!"node {val} L:({BinTreeIntToString l})"
  | node val nil r   => s!"node {val} R:({BinTreeIntToString r})"
  | node val l r     => s!"node {val} L:({BinTreeIntToString l}) R:({BinTreeIntToString r})"

instance : ToString BinTreeInt where
  toString := BinTreeIntToString

def insert (x : Int) (tree : BinTreeInt) : BinTreeInt :=
  match tree with
  | nil          => singTree x
  | node val l r =>
    if x < val then
      match l with
      | nil        => node val (singTree x) r
      | node _ _ _ => node val (insert x l) r
    else match r with
      | nil        => node val l (singTree x)
      | node _ _ _ => node val l (insert x r)

def tree3 := node 4 (singTree 1) (node 6 (singTree 5) (singTree 9))

#eval tree3
#eval insert 2 tree3
#eval insert 42 tree3


#eval nil
#eval node 4 nil nil
#eval node 1 (node 2 nil nil) nil

#check "Ola mundo" --> String
#check 42          --> Nat

#check String
#check Nat

#check Type

inductive Um where
 | cara1

structure Pair (α : Type 1) (β : Type 1) where
  pair ::
  x : α
  y : β
open Pair

-- #check pair "oi" String
#check pair Nat String

def head : List α → Option α
 | []     => none
 | a :: _ => some a

#eval head [1,2,3]
#eval head ([] : List Int)
#eval some 3
#eval some (some (some 3))
#eval some (some (none : Option Int))
#eval some (none : Option (Option Int))
#eval (none : (Option (Option (Option Int))))

#check (· = ·)  --> fun x1 x2 => x1 = x2  : ?m.4509 → ?m.4509 → Prop
#check (· == ·) --> fun x1 x2 => x1 == x2 : ?m.4523 → ?m.4523 → Bool

#check 2 < 4
#eval if 2 < 4 then 1 else 2

def Nat.comp : Nat → Nat → Ordering
  | 0, 0         => Ordering.eq
  | _, 0         => Ordering.gt
  | 0, _         => Ordering.lt
  | n + 1, m + 1 => Nat.comp n m


class MyHashable (α : Type) where
  hash : α → UInt64
  eqPreserv : ∀(a₁ a₂ : α), a₁ = a₂ →
                hash a₁ = hash a₂

def hashNat : Nat → UInt64
  | 0     => 0
  | n + 1 => mixHash 1 (hashNat n)

instance : Hashable Nat where
  hash := hashNat

inductive BinTree (α : Type) where
| nil  : BinTree α
| node : α → BinTree α → BinTree α → BinTree α


def BinTreeToString [ToString α] : BinTree α → String
  | BinTree.nil => ""
  | BinTree.node val BinTree.nil BinTree.nil =>
    s!"node {val}"
  | BinTree.node val l BinTree.nil =>
    s!"node {val} L:({BinTreeToString l})"
  | BinTree.node val BinTree.nil r
    => s!"node {val} R:({BinTreeToString r})"
  | BinTree.node val l r =>
    s!"node {val} L:({BinTreeToString l}) R:({BinTreeToString r})"


instance [ToString α] : ToString (BinTree α) where
  toString := BinTreeToString

def three := BinTree.node 'a' BinTree.nil BinTree.nil
def four  := BinTree.node 'b' three BinTree.nil
def five  := BinTree.node 'c' four three

#eval five

def is_id {α : Type} (f : α → α) : Prop :=
   ∀(a : α), f a = a

#check id
#check id 3
#eval  id 3


class Funktor (F : Type → Type) where
  -- Operations:
  map : {α β : Type} → (α → β) → F α → F β

  mapConst {α β : Type} (x : α) (coll : F β) : F α :=
    map (fun _ => x) coll

 -- Laws:
  id_law   : ∀(f_a : F α), map id f_a = fa
  comp_law : ∀(f : α → β), ∀(g : β → γ), ∀(f_a : F α),
               map (g ∘ f) f_a = map g (map f f_a)

  -- Being associative was a theorem then?


structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

-- chapei:
-- def hAppendListWithNonEMptyList (xs : List α) (ys : NonEmptyList α) : NonEmptyList α :=
--   match xs with
--   | []      => ys
--   | x :: xs => hAppendListWithNonEMptyList xs {head := x, tail := ys.head :: ys.tail}

-- how to do this using let rec or something like that? (ok i didnt need it..)
instance : HAppend (List α) (NonEmptyList α) (NonEmptyList α) where
  hAppend xs ys :=
    match xs with
    | []      => ys
    | x :: xs =>  {head := x, tail := xs ++ ys.head :: ys.tail}

#eval [1, 2, 3] ++ NonEmptyList.mk 4 [5,6]
