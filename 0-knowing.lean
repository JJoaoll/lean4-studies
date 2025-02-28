#eval 1 + 2
#eval 1 + 2 * 5
-- wrong:
-- eval String.append("Hello, ", "Lean!")
#eval String.append "Hello, " "Lean!"
#eval String.append "great " (String.append "oak " "tree")
#eval String.append "it is " (if 1 > 2 then "yes" else "no")

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
