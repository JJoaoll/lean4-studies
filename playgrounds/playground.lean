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
def last? (l : List α) : Option α :=
    match l with
      | []     => none
      | [x]    => some x
      | _ :: xs => last? xs

#eval last? [1, 2, 3, 4]
#eval last? [1]
#eval (last? [] : Option Int)
#eval last? ([] : List Int)

-- Write a function that finds the first entry in a list that satisfies a given predicate.
-- Start the definition with
def List.findFirst? {α : Type} (p : α → Bool) : List α → Option α
    | []      => none
    | x :: xs =>
        if   p x
        then some x
        else List.findFirst? p xs


#eval List.findFirst? (· > 3) [1, 2, 3]
#eval List.findFirst? (λx => x > 3) [1, 2, 3]
#eval List.findFirst? (· > 3) [1, 2, 3, 4, 5, 6, 7]
#eval List.findFirst? (λx => x > 3) [1, 2, 3, 4, 5, 6, 7]

-- Write a function Prod.swap that swaps the two fields in a pair.
-- Start the definition with
-- def Prod.swap {α β : Type} (pair : α × β) : match pair with | (a, b) => β × α :=
-- def Prod.swap {α β : Type} (pair : α × β) : β × α :=
--     match pair with
--       | (a, b) => (b, a)

-- Rewrite the PetName example to use a custom datatype
-- and compare it to the version that uses Sum.

-- BAD:
-- def PetName : Type := String ⊕ String
-- def animals : List PetName :=
--   [Sum.inl "Spot", Sum.inr "Tiger", Sum.inl "Fifi", Sum.inl "Rex",
--   Sum.inr "Floof"]
-- def howManyDogs (pets : List PetName) : Nat :=
--   match pets with
--   | [] => 0
--   | Sum.inl _ :: morePets => howManyDogs morePets + 1
--   | Sum.inr _ :: morePets => howManyDogs morePets

-- Better:
inductive PetName where
  | Dog (name : String) : PetName
  | Cat (name : String) : PetName
deriving Repr

def animals : List PetName :=
    [PetName.Dog "Spot", PetName.Cat "Tiger", PetName.Dog "Fifi",
     PetName.Dog "Rex" , PetName.Cat "Floof"]

#eval animals

def howManyDogs : List PetName → Nat
    | []                        => 0
    | PetName.Dog _ :: morePets => howManyDogs morePets + 1
    | PetName.Cat _ :: morePets => howManyDogs morePets

#eval howManyDogs animals
-- More verbous is fabulous somethimes <3

-- Write a function zip that combines two lists into a list of pairs.
-- The resulting list should be as long as the shortest input list.
-- Start the definition with
-- def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
def zip : List α → List β → List (α × β)
    | x :: xs, y :: ys => (x, y) :: zip xs ys
    | _      , _       => []

#eval  zip [1, 2, 3] animals
#check zip
#check zip [1, 2, 3] -- interesting. The metavar thing, i mean.
#check zip [1, 2, 3] animals

-- Write a polymorphic function take that returns the first n
-- entries in a list, where n is a Nat. If the list contains fewer
-- than n entries, then the resulting list should be the input list.

def take : Nat → List α → List α
    | Nat.succ n, x :: xs  => x :: take n xs
    | _, _                 => []

-- should yield ["bolete", "oyster"]
#eval take 3 ["bolete", "oyster"]
-- should yield ["bolete"].
#eval take 1 ["bolete", "oyster"]

-- Using the analogy between types and arithmetic,
-- write a function that distributes products over sums.
-- In other words, it should have type α × (β ⊕ γ) → (α × β) ⊕ (α × γ).
def distribute : α × (β ⊕ γ) → (α × β) ⊕ (α × γ)
    | (a, Sum.inl b) => Sum.inl (a, b)
    | (a, Sum.inr c) => Sum.inr (a, c)

-- Using the analogy between types and arithmetic,
-- write a function that turns multiplication by two into a sum.
-- In other words, it should have type Bool × α → α ⊕ α.
def times2 : Bool × α → α ⊕ α
    | (Bool.true , a) => Sum.inl a
    | (Bool.false, a) => Sum.inr a

#eval times2 (Bool.true, 3)

def var     := "var"
def funtest := λ(_ : Nat) => 3


def unzip : List (α × β) → List α × List β
  | []            => ([], [])
  | (x, y) :: xys =>
    let unzipped : List α × List β := unzip xys; (x :: unzipped.fst, y :: unzipped.snd)

#eval unzip [(1, 2), (3, 4)]

#check λ
  | 0 => none
  | n + 1 => some n
def unnzip : List (α × β) → List α × List β
  | []            => ([], [])
  | (x, y) :: xys =>
    let (xs, ys) := unzip xys
    (x :: xs, y :: ys)


#check (·, ·)
#check (·, ·) 2
#check (·, ·) 2  3
#eval  (·, ·) 2  3


--- IO Things:

def twice (action : IO Unit) : IO Unit := do
 action
 action

#eval twice (IO.println "shy")

def test_eval_main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  stdout.putStrLn "How would you like to be addressed?"
  let input ← stdin.getLine
  let name := input.dropRightWhile Char.isWhitespace
  stdout.putStrLn s!"Hello, {name}!"

#eval test_eval_main

def nTimes (action : IO Unit) : Nat → IO Unit
  | 0     => pure ()
  | n + 1 => do
    action
    nTimes action n

#eval nTimes (IO.println "shy") 1
def countdown : Nat → List (IO Unit)
  | 0 => [IO.println "Blast off!"]
  | n + 1 => IO.println s!"{n + 1}" :: countdown n

def hc :=
  match countdown 0 with
    | []     => pure ()
    | a :: _ => a

#eval hc

-- the "sequenceAll.."
def runActions : List (IO Unit) → IO Unit
  | [] => pure ()
  | act :: actions => do
    act
    runActions actions

#eval runActions $ countdown 5

def safeHead (l : List α) : match l with | [] => Unit | _ => α :=
   match l with
    | []      => ()
    | x :: _  => x

def five? (l : List α) (_ : match l with | [] => Unit | _ => α) : Nat :=
  5
#check safeHead

def four : (n : Nat) → (n = 4 : Prop) : Nat :=
    4

#eval animals
#eval animals[4]?
#eval animals[5]?

theorem t1 : 2 + 3 = 5  := rfl
theorem t2 : 15 - 8 = 7 := rfl
theorem t3 : "Hello, ".append "world" = "Hello, world" := rfl
-- theorem t4 : 5 < 18 := rfl

theorem t5 : 2 + 3 = 5  := by simp
theorem t6 : 15 - 8 = 7 := by simp
-- theorem t7 : "Hello, ".append "world" = "Hello, world" := by simp
theorem t8 : 5 < 18 := by simp

def fun_that_look_fifth (l : List α) (ok : l.length > 4) : α := l[4]

#check fun_that_look_fifth animals
#eval fun_that_look_fifth [1, 2, 3, 4, 5] (by simp)
def fromOneToFive := [1, 2, 3, 4, 5]
#eval fun_that_look_fifth fromOneToFive (by rw [fromOneToFive]; simp)
-- #eval fun_that_look_fifth (animals[0] :: animals) (by rw [animals];)
-- def animals2 := animals[0] :: animals
-- #eval fun_that_look_fifth animals2 (by rw [animals2]; simp; rw [animals.length])

class Plus (α : Type) where
  plus : α → α → α

instance : Plus Nat where
  plus := Nat.add

#eval Plus.plus 5 3
open Plus (plus)
#eval plus 5 3

inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos

def Pos.plus : Pos → Pos → Pos
  | Pos.one, k => Pos.succ k
  | Pos.succ n, k => Pos.succ (n.plus k)

def seven : Pos :=
  Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one)))))

instance : Plus Pos where
  plus := Pos.plus

instance : Add Pos where
  add := Pos.plus
#check Int

instance : Add Type where
  add := Sum

#check Int + String

def fourteen : Pos := seven + seven

#check 5
#check "midoriya"
#check String
#check Type

class Default (α : Type) where
  default : α

instance : Default Nat where
  default := 0

class Fool (α : Type) where
  fool : α → Nat

instance : Fool String where
  fool := fun _ => 5

instance : Fool Int where
  fool := fun _ => 6

open Fool
#eval fool "ola mundo"
#eval fool (5 : Int)

#check (· × ·)
#check Prod
#check Prod Int Nat
#check Int × Nat
#check Int ⊕ Nat

instance : Add String where
 add := (· ++ ·)

#eval "ola, " + "mundo!"

def f (b : Bool) : Type :=
  if b then String
       else Bool

def posToString (atTop : Bool) (p : Pos) : String :=
  let paren s := if atTop then s else "(" ++ s ++ ")"
  match p with
  | Pos.one => "Pos.one"
  | Pos.succ n => paren s!"Pos.succ {posToString false n}"

class Foo (n : Nat) where
  const : Nat
open Foo

instance : Foo 5 where
  const := 42
instance : Foo 4 where
  const := 53

#eval const 5
#eval const 4
-- #eval Foo.const 4
--
#check 3
#check (3, 3)


instance : Add String where
  add := (· ++ ·)

instance : Add Type where
  add := Sum

#check String + Char
#eval "banana " + "maca"

class Funktor (f : Type → Type) where
  fmap : (α → β) × f α → f β


def listMap : (α → β) × List α → List β
 | (f, as') =>
   match as' with
     | []      => []
     | a :: as => f a :: listMap (f, as)

def test := [1, 2, 3, 4]
#eval listMap ((· + 1), test)
#eval listMap ((· * 2), test)
#eval listMap (fun _ => "oi", test)

structure User where
 id     : Int
 name   : String
 salary : Float
deriving Repr

def users := [User.mk 0 "Joao" 3000, User.mk 1 "Pedro" 1500]
#eval users
#eval listMap (User.salary, users)

instance : Funktor List where
  fmap := listMap

-- def optionalMap : (α → β) → (Optional α → Optional β)
open Functor
#check Functor.map
#eval (· + 1) <$> [1, 2, 3, 4]
