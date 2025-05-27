import Lean

open Lean

set_option pp.universes true in
set_option pp.explicit true in
notation "pure" => pure -- pure azul, por favor? so falta arrumar a prioridade

#check pure
#check return

#check Expr
#print Expr

-- Exercises

--     Create expression 1 + 2 with Expr.app.

def zero : Expr := (Expr.const ``Nat.zero [])
def one  : Expr := .app (.const ``Nat.succ []) zero
def two := Expr.app (.const ``Nat.succ []) one

def Ex1 : Expr := .app (.app (.const ``Nat.add []) one) two
elab "Ex1" : term => return Ex1

#check @Ex1
#eval Ex1

--     Create expression 1 + 2 with Lean.mkAppN.
#check mkAppN (.const ``Nat.add []) #[one, two]
def Ex2 := mkAppN (.const ``Nat.add []) #[one, two]
elab "Ex2" : term => pure Ex2

#check Ex2
#eval Ex2

--     Create expression fun x => 1 + x.
#check Expr.lam
def Ex3 :=
  Expr.lam `x (.const ``Nat [])
    (mkAppN (.const ``Nat.add []) #[mkNatLit 1, .bvar 0])
    BinderInfo.default
elab "Ex3" : term => pure Ex3

#check Ex3
#eval Ex3 4

--     [De Bruijn Indexes] Create expression fun a, fun b, fun c, (b * a) + c.
def nat := Expr.const ``Nat []
def Ex4 : Expr :=
  .lam `a nat
    (.lam `b nat
      (.lam `c nat
        (mkAppN (.const ``Nat.add []) #[mkAppN (.const ``Nat.mul []) #[.bvar 1, .bvar 2], .bvar 0])
        BinderInfo.default)
        BinderInfo.default)
        BinderInfo.default
elab "Ex4" : term => pure Ex4

#check Ex4
#eval Ex4 3 4 5

--     Create expression fun x y => x + y.
#check Lean.mkLambdaEx
  #check Expr.lam
def Ex5 : Expr :=
  .lam `x nat
    (.lam `y nat
      (mkAppN (.const ``Nat.add [])
      #[.bvar 1, .bvar 0])
      BinderInfo.default)
    BinderInfo.default
elab "Ex5" : term => pure Ex5

#check Ex5

--     Create expression fun x, String.append "hello, " x.
#check mkAppN
#check mkStrLit

def Ex6 : Expr :=
  .lam `x (.const ``String [])
    (mkAppN (.const ``String.append []) #[mkStrLit "hello, ", .bvar 0])
    BinderInfo.default
elab "Ex6" : term => pure Ex6

#check Ex6
#eval Ex6 "world!"

--     Create expression ∀ x : Prop, x ∧ x.
--     Create expression Nat → String.
--     Create expression fun (p : Prop) => (λ hP : p => hP).
--     [Universe levels] Create expression Type 6.
