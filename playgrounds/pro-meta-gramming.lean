import Lean

open Lean

-- set_option pp.universes true in
-- set_option pp.explicit true in
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
#check Expr.forallE
#check Prop
#check Expr.const ``Nat []
#check Expr.sort 0
def tst1 : Expr := .sort 0
elab "tst1" : term => pure tst1

#check tst1
#check Expr.forallE
#print Expr

#check (x : Nat) → Nat
#check ∀ x : Prop, x ∧ x
#check ((x : Prop) → x ∧ x) = true
#check "Oi"

def tst2 : Expr :=
  .forallE `x (.const ``Nat []) (mkAppN (.const ``Nat.add []) #[.bvar 0, mkNatLit 2])
    BinderInfo.default
elab "tst2" : term => pure tst2

def Ex7 : Expr :=
  .forallE `x (.sort 0) (mkAppN (.const ``And []) #[.bvar 0, .bvar 0])
    BinderInfo.default
elab "Ex7" : term => pure Ex7
#check Ex7
variable (p : Prop)
#check Ex7 = true
#check Ex7 = true
#check And
#check And.intro

--     Create expression Nat → String.
#print Expr
open Expr in
def Ex8 : Expr :=
  forallE `x (const ``Nat []) (const ``String [])
    BinderInfo.default
elab "Ex8" : term => pure Ex8
#check Ex8

--     Create expression fun (p : Prop) => (λ hP : p => hP).
#check Expr.lam
open Expr in
def Ex9 : Expr :=
  lam `p (sort 0) (lam `hP (bvar 0) (bvar 1) BinderInfo.default)
    BinderInfo.default

elab "Ex9" : term => pure Ex9
#check Ex9

--     [Universe levels] Create expression Type 6.
def Ex10 : Expr :=
  .sort 7
elab "Ex10" : term => pure Ex10

#check Ex10
