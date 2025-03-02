#eval 1 + 2
#eval 1 + 2 * 5
-- wrong:
-- eval String.append("Hello, ", "Lean!")
#eval String.append "Hello, " "Lean!"
#eval String.append "great " (String.append "oak " "tree")
#eval String.append "it is " (if 1 > 2 then "yes" else "no")



def v := 4


#check v
#eval Nat.succ 4
#eval v + 1 - 1


-- "exercises"
#eval 42 + 19
#eval String.append "A" (String.append "B" "C")
#eval String.append (String.append "A" "B") "C"
#eval if 3 == 3 then 5 else 7
#eval if 3 == 4 then "equal" else "not equal"

#eval (1 + 2 : Nat)
#eval 1 - 2
#eval (1 - 2 : Int)
#check (1 - 2 : Int)
-- error:
--#check String.append "hello" [" ", "world"]
def hello := "Hello"
def lean : String := "Lean"
#eval String.append (String.append hello (String.append ", " lean)) "!"
def succ (n : Nat) : Nat :=
   n + 1
#eval succ 3
 def maximum (n : Nat) (k : Nat) : Nat :=
      if n < k then
        k
      else n
#check succ
#check maximum
#check maximum 3

-- Exercises

--     Define the function joinStringsWith with type
--     String -> String -> String -> String that creates a new string
--     by placing its first argument between its second and third arguments.
--     joinStringsWith ", " "one" "and another" should evaluate to "one,
--     and another".
def joinStringsWith (str1 str2 str3 : String) : String :=
     String.append str2 (String.append str1 str3)

#eval joinStringsWith ", " "one" "and another"
#check joinStringsWith

--     What is the type of joinStringsWith ": "? Check your answer with Lean.
--     Define a function volume with type Nat → Nat → Nat → Nat that
--     computes the volume of a rectangular prism with the given height,
--     width, and depth.
-- sorry, geometry? not here! :PP
def Str : Type := String
def aStr : Str := "Look at me, i'm a String! wait, i'm a \"Str\"?.. "

#eval aStr
abbrev N : Type := Nat
def thirtyNine : N := 39
#eval thirtyNine


#eval 1.2
#check 1.2
#check 0.0
#check 0
#check (0 : Float)

structure Point where
  x : Float
  y : Float
deriving Repr

def    origin : Point := { x := 0.0, y := 0.0 }
#eval  origin
#check origin
#eval origin.x
#eval origin.y

def distance (p1 : Point) (p2 : Point) : Float :=
  Float.sqrt (((p2.x - p1.x) ^ 2.0) + ((p2.y - p1.y) ^ 2.0))

#eval distance { x := 1.0, y := 2.0 } { x := 5.0, y := -1.0 }
#check { x := 0.0, y := 0.0 : Point}
#check Point.mk 1.5 2.8
#eval Point.mk 1.5 2.8
#check (Point.mk)
#check Point.x origin
#check (Point.x) origin


-- NOOO WAYYY LOOK AT THAT:

#eval 2.+ 3
#eval "Hello, ".append "World!"


-- Some struct exercises:
structure RectangularPrism where
  height : Float
  width  : Float
  depth  : Float
deriving Repr

#check (RectangularPrism.mk)

def volume (r : RectangularPrism) : Float :=
    r.height * r.width * r.depth

#check volume

structure Segment where
  x₁ : Float
  x₂ : Float
deriving Repr

def lenght (s : Segment) : Float :=
    if s.x₁ > s.x₂
      then s.x₁ - s.x₂
      else s.x₂ - s.x₁


#check repr



inductive MyNat where
  | zero           : MyNat
  | succ (n : MyNat) : MyNat
deriving Repr

#eval MyNat.zero
#eval MyNat.succ MyNat.zero
#eval MyNat.zero.succ.succ.succ |> MyNat.succ


def isZero (n : Nat) : Bool :=
   match n with
   | Nat.zero   => true
   | Nat.succ _ => false

structure Point3D where
  x : Float
  y : Float
  z : Float
deriving Repr


def depth (p : Point3D) : Float :=
    match p with
    | Point3D.mk _ _ d => d

-- def depth (p : Point3D) : Float :=
--    match p with
--    | { x:= _, y := _, z := d } => d

--  no termination:
-- def evenLoops (n : Nat) : Bool :=
--   match n with
--   | Nat.zero => true
--   | Nat.succ k => not (evenLoops n)


#check Type
#check Type 1
#check Type 32
structure PPoint (α : Type) where
   x : α
   y : α
deriving Repr

def natOrigin : PPoint Nat :=
    PPoint.mk Nat.zero Nat.zero
--   { x := Nat.zero, y := Nat.zero }

#eval natOrigin
def replaceX (α : Type) (point : PPoint α) (newX : α) : PPoint α :=
    { point with x := newX }

#check (replaceX)
#check replaceX Nat
#check replaceX Nat natOrigin
#check replaceX Nat natOrigin 5

#eval replaceX Nat natOrigin 5


inductive Sign where
  | pos
  | neg

def posOrNegThree (s : Sign) : match s with | Sign.pos => Nat | Sign.neg => Int :=
  match s with
  | Sign.pos => (3 : Nat)
  | Sign.neg => (-3 : Int)

 def length? {α : Type} (xs : List α) : Nat :=
      match xs with
      | [] => 0
      | _ :: ys => Nat.succ (length? ys)

#eval length? [1, 2, 3]
#eval [1, 2, 3].length

#check length?
#check length? (α := Int)

def List.headd? {α : Type} (xs : List α) : Option α :=
  match xs with
  | [] => none
  | y :: _ => some y

#eval [1,2,3,4].head?
-- error
-- #eval [].head?
#eval [].head? (α := Nat)
#eval ([] : List Int).head?

#eval ()
#check (() : Unit)

inductive Emptyy where
#check Emptyy
--Write a function to find the last entry in a list. It should return an Option.
def last (l : List α) : Option α :=
    match l with
      | []     => none
      | [x]    => some x
      | _ :: xs => last xs

#eval last [1, 2, 3, 4]
#eval last [1]
#eval (last [] : Option Int)
#eval last ([] : List Int)



-- Write a function that finds the first entry in a list that satisfies a given predicate. Start the definition with def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α :=
-- Write a function Prod.swap that swaps the two fields in a pair. Start the definition with def Prod.swap {α β : Type} (pair : α × β) : β × α :=
-- Rewrite the PetName example to use a custom datatype and compare it to the version that uses Sum.
-- Write a function zip that combines two lists into a list of pairs. The resulting list should be as long as the shortest input list. Start the definition with def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=.
-- Write a polymorphic function take that returns the first n
-- entries in a list, where n
-- is a Nat. If the list contains fewer than n entries, then the resulting list should be the input list. #eval take 3 ["bolete", "oyster"] should yield ["bolete", "oyster"], and #eval take 1 ["bolete", "oyster"] should yield ["bolete"].
-- Using the analogy between types and arithmetic, write a function that distributes products over sums. In other words, it should have type α × (β ⊕ γ) → (α × β) ⊕ (α × γ).
-- Using the analogy between types and arithmetic, write a function that turns multiplication by two into a sum. In other words, it should have type Bool × α → α ⊕ α.
