namespace Set

structure Set (α : Type) where
  pred : α → Prop
deriving Inhabited

macro "{ " x:ident " : " t:term " | " y:term " }" : term =>
  `(Set.mk (fun $x : $t => $y))

notation:100 x " ∈ " A => Set.pred A x
notation:100 x " ∉ " A => ¬(x ∈ A)

def Set.void : Set α := { x : α | x ≠ x }

notation " ∅ " => Set.void

def Set.union : Set α × Set α → Set α
  | (A, B) => { x : α | (x ∈ A) ∨ (x ∈ B) }

def Set.intersection : Set α × Set α → Set α
  | (A, B) => { x : α | (x ∈ A) ∧ (x ∈ B) }

def Set.subtraction : Set α × Set α → Set α
  | (A, B) => { x : α | (x ∈ A) ∧ (x ∉ B)}

instance (α : Type) : Union (Set α) where
  union a b := Set.union (a, b)

instance (α : Type) : Inter (Set α) where
  inter a b := Set.intersection (a, b)

infixr:110 " / " => Set.subtraction

-- Sejam 𝔸 : Set (Set α), A : Set α, chamamos 𝔸 de partição
-- de A sse:
-- 1. ⋃ 𝔸 = A
-- 2. 𝔸 disj 2 a 2
-- 3. ∀ X ∈ 𝔸, X habitado.

-- 1. ⋃ 𝔸 = A
def Set.Union : Set (Set α) → Set α
  | 𝒜 => { a : α | ∃ A : Set α, (A ∈ 𝒜) ∧ (a ∈ A) }

notation:110 "⋃" 𝒜 => Set.Union 𝒜

-- 2 𝔸 disj 2 a 2
def Set.disj2_2 : Set (Set α) → Prop
  | 𝒜 => ∀ (A B : Set α), ((A ∈ 𝒜) ∧ (B ∈ 𝒜)) → (A ∩ B = Set.void)


def habitado : Set α → Prop
  | A => ∃ x : α, x ∈ A

notation A " eh_habitado" => habitado A

end Set

section
universe u
class Linorder (α : Type u) where
  R : α → α → Prop

  -- laws
  refl      : ∀ a, R a a
  trans     : ∀ a b c, R a b → R b c → R a c
  antisymm  : ∀ a b, R a b → R b a → a = b
  linearity : ∀ a b, R a b ∨ R b a

end

instance [Linorder α] : LE α where
  le x y := Linorder.R x y

instance [Linorder α] : LT α where
  lt x y := Linorder.R x y ∧ x ≠ y

section
universe u
variable (α : Type u) [Linorder α] [DecidableLE α] [BEq α]

def List.isSorted : List α → Prop
  | [] => True
  | x::ys => ∀ y : α, (ys.elem y → x ≤ y) ∧ ys.isSorted

def List.sorted : List α → Bool
  | [] => true
  | x::ys => ys.all (x ≤ ·) && ys.sorted

theorem t1 : ∀ l : List α, l.sorted ↔ l.isSorted := by
  sorry
end

section
universe u
variable (α : Type u) [Linorder α] [DecidableLE α] [BEq α]
-- Lets specify whats a sort should do, but not as a class
structure Sorter {α : Type u} [Linorder α] [DecidableLE α] [BEq α] where

-- TODO: generalizar isso pra mais coisas do que apenas Listas!!! (foldable?) (functor?)
  sort : List α → List α
  law1 : ∀ (xs : List α), (sort xs).isSorted
  -- law2 : ∀ (xs : List α), mset (sort xs) = mset xs



end
