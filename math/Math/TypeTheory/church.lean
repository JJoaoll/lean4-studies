import Mathlib.Data.Set.Basic
import Mathlib.Data.Multiset.Basic

namespace Church -- 1990

section Λ
universe u

-- Deﬁnition 1.3.2 (The set Λ of all λ-terms)
inductive Lambda (Var : Type u) where
  | var (_ : Var)
  | app (M N : Lambda Var)
  | abs (_ : Var) (M : Lambda Var)
deriving DecidableEq open Lambda

-- because of the DecidableEq, whats gonna happen is that it'll serve us
--> just to follow the book. I know thats a bit weird.
notation x " ≡ " y =>  x = y
notation:20 "λ" x ". " M  => Lambda.abs x M

-- sintaticaly
-- Λ = V |(ΛΛ)|(λV . Λ)

-- M [x := N ] --> "substituia todas as ocorrencias de <x> em <M> por <N>"
def subst [DecidableEq α] (x : α) (M N : Lambda α) : Lambda α  :=
  match M with
  | var x'    => if x = x' then N else var x'
  | app M₁ M₂ => app (subst x M₁ N) (subst x M₂ N)
  | abs y M'  => if x = y then M else abs y (subst x M' N)

notation M " [ " x " := " N " ] " => subst x M N

-- def β_reduction [DecidableEq α] (expr : Lambda α) : Lambda α :=
--   match expr with
--   | app (abs x M) N => M [x := N]
--   | ex => ex

def var₁ := var 'x'
def var₂ := var 'y'
def var₃ := var 'z'

def app₁ := app var₁ var₁
def app₂ := app var₁ var₂
def app₃ := app app₁ app₂

def abs₁ := abs 'x' app₁
def abs₂ := abs 'y' app₃
def abs₃ := abs 'z' abs₁
def abs₄ := abs 'x' abs₂


-- weird error rejected
def util : Lambda Char → String
  | var x => toString x
  | app N M => util N ++ util M
  | abs x M => "(λ" ++ toString x ++ ". " ++ util M ++ ")"

instance : ToString (Lambda Char) where
 toString
   | var x => toString x
   | app N M => util N ++ util M
   | abs x M => "(λ" ++ toString x ++ ". " ++ util M ++ ")"

end Λ

#eval abs₄
#eval var₁
-- #eval β_reduction $ app abs₄ var₃
#eval abs₃
-- #eval (β_reduction $ app abs₄ var₃) ['z' := abs₃]


#print DecidableEq

section Subterms

open Lambda

-- Deﬁnition 1.3.5 (Multiset of subterms; Sub)
-- (1) (Basis) Sub(x) = {x}, for each x ∈ V .
-- (2) (Application) Sub((M N )) = Sub(M ) ∪ Sub(N ) ∪ {(M N )}.
-- (3) (Abstraction) Sub((λx . M )) = Sub(M ) ∪ {(λx . M )}.
-- Based on the book, i'm interpreating it as a sum of bags and not as a union.
def Lambda.sub [DecidableEq α] (expr : Lambda α) : Multiset (Lambda α) :=
  let s := singleton expr
  match expr with
  | var _   => s
  | app M N => M.sub + N.sub + s
  | abs _ M => M.sub + s

-- We call L a subterm of M if L ∈ Sub(M ).
notation L " is_a_subterm_of " M => L ∈ Lambda.sub M

universe u
variable (α : Type u) [DecidableEq α]
variable (M N L : Lambda α)

theorem Lambda.sub_refl [DecidableEq α] :
  ∀ (M : Lambda α), M is_a_subterm_of M := by {
  -- intros M
  -- unfold Lambda.sub
  -- cases M
  -- case var x =>
  --   simp [MultiSet.singleton, Bag.has]
  -- case app N M =>
  --   simp [Bag.has]
  --   have := sing_one (N.app M)
  --   have h : (MultiSet.singleton (N.app M)).count (N.app M) > 0 := by simp [this]
  --   sorry
  sorry
}

theorem Lambda.sub_trans [DecidableEq α] : ∀ (L M N : Lambda α),
  (L is_a_subterm_of M) ∧ (M is_a_subterm_of N)
  → L is_a_subterm_of N := by {
  intro L M N
  intro h
  repeat sorry
}

-- 1.3.8
def proper_subterm [DecidableEq α] (L M : Lambda α) :=
  (L is_a_subterm_of M) ∧ ¬(L ≡ M)

end Subterms

-- Notation 1.3.10 − Parentheses in an outermost position may be omitted,
-- so M N stands for λ-term (M N ) and λx . M for (λx . M ).8
-- Untyped lambda calculus
-- − Application is left-associative, so M N L is an abbreviation for ((M N )L).
-- − Application takes precedence over abstraction, so we can write λx . M N in-
-- stead of λx . (M N ).
-- − Successive abstractions may be combined in a right-associative way under
-- one λ, so we write λxy . M instead of λx . (λy . M ).
section FreeVariables
open Lambda
-- Deﬁnition 1.4.1 (FV, the set of free variables of a λ-term) -- page 8
def Lambda.FV [DecidableEq α] (L : Lambda α) : Set α :=
  match L with
  | var x => {x}
  | app M N => FV M ∪ FV N
  | abs x M => (FV M) \ {x}

-- (1) (Variable) FV (x) = {x},
-- (2) (Application) FV (M N ) = FV (M ) ∪ FV (N ),
-- (3) (Abstraction) FV (λx . M ) = FV (M ) \ {x}.

-- --Deﬁnition 1.4.3 (Closed λ-term; combinator; Λ0 ) -- page 9
def Lambda.closed [DecidableEq α] (M : Lambda α) := M.FV = ∅
-- The λ-term M is closed if F V (M ) = ∅. A closed λ-term is also called a
-- combinator . The set of all closed λ-terms is denoted by Λ0 .
-- Example: λxyz . xxy and λxy . xxy are closed λ-terms; λx . xxy is not.

end FreeVariables

-- In order to describe this process formally, we deﬁne a relation called α-      -- page 9
-- conversion or α-equivalence. It is based on the possibility of renaming binding
-- (and bound) variables (cf. Hindley & Seldin, 2008, p. 278).

-- Deﬁnition 1.5.1 (Renaming; M x→y ; =α )
-- Let M x→y denote the result of replacing every free occurrence of x in M by y.
-- The relation ‘renaming’, expressed with symbol =α , is deﬁned as follows:
-- λx . M =α λy . M x→y , provided that y ∈ FV (M ) and y is not a binding
-- variable in M .
-- One says in this case: ‘λx . M has been renamed as λy . M x→y ’.
--
-- Meta things that i'll have to


-- Renaming in Deﬁnition 1.5.1 applies to the full λ-term only. In order to allow -- page 10
-- it more generally, we extend this deﬁnition to the following one:
-- Deﬁnition 1.5.2 (α-conversion or α-equivalence, =α )
-- (1) (Renaming) λx . M =α λy . M x→y as in Deﬁnition 1.5.1, under the same
-- conditions,
-- (2) (Compatibility) If M =α N , then M L =α N L, LM =α LN and, for
-- arbitrary z, λz . M =α λz . N ,
-- Isnt the next ones demonstrable?
-- (3a) (Reﬂexivity) M =α M ,
-- (3b) (Symmetry) If M =α N then N =α M ,
-- (3c) (Transitivity) If both L =α M and M =α N , then L =α N .



-- Deﬁnition 1.5.4 (α-convertible; α-equivalent; α-variant)
-- If M =α N , then M and N are said to be α-convertible or α-equivalent. M is
-- called an α-variant of N (and vice versa).
end Church -- 1933
