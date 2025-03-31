
inductive Tipe : Type 1 where
| n
| z
| f
| s
| c
| t

def Op (α : Type) (ar : Nat) := List α → α

#eval 3

inductive SyntaxTree where
| leaf   (t : Tipe) : SyntaxTree
| branch (l : List SyntaxTree) : Op α ar → l.length = ar → SyntaxTree
#check List.all

def typecheck : SyntaxTree → Type :=
  sorry

def eval : SyntaxTree → α :=
  sorry

-- open Operator
-- open SyntaxTree

-- def ex0 := branch (leaf 3) times (leaf 4)
-- def ex1 := branch (leaf 3) plus (leaf 4)
-- def ex2 := branch ex1 times (leaf 5)
-- def ex3 := branch ex1 times ex2
-- def ex4 := branch ex0 times ex2

-- def eval_string : SyntaxTree → String
--   | leaf n        => toString n
--   | branch l op r =>
--   let par (str : String) := s!"({str})"
--   par (match op with
--   | plus  => (eval_string l) ++ " plus "  ++ (eval_string r)
--   | times => (eval_string l) ++ " times " ++ (eval_string r))

-- def eval_times : SyntaxTree → SyntaxTree
--   | leaf n           => leaf n
--   | branch l plus r  => branch (eval_times l) plus (eval_times r)
--   | branch l times r =>
--     let (l', r') := (eval_times l, eval_times r)
--     match l', r' with
--     | leaf n, leaf m => leaf (n * m)
--     | _     , _      => branch l' times r'

-- #eval eval_string ex3
-- #eval eval_string ex4
-- #eval eval_string (eval_times ex4)

---------------------------------------------------------------------------------------------------------------------------

inductive Foo : Type → Type 1 where
| numb : Int  → Foo Int
| bool : Bool → Foo Bool
| plus : Foo Int  → Foo Int → Foo Int
| not  : Foo Bool → Foo Bool
| ite  : Foo Bool → Foo α → Foo α → Foo α
deriving Repr

open Foo

#eval  numb 3
#eval  ite (bool true) (numb 3) (numb 4)
#check numb 3
