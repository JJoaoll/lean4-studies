-- Functor -> Applicatives -> Monads
namespace show_case
  def divides x y := ∃ (k : Nat), x * k = y
  infix:1000 "|" => divides
  -- infix:500 "&"  => And
  -- infix:500 "ou" => Or
  -- notation x"|"y => divides x y

  theorem div_trans : ∀ (x y z : Nat), x|y ∧ y|z → x|z := by
  intros a b c
  intro h
  let h₁ := And.left h
  let h₂ := And.right h
  obtain ⟨k, hk⟩ := h₁
  obtain ⟨q, hq⟩ := h₂
  rw [divides]
  exists (k * q)
  rw [← Nat.mul_assoc]
  rw [hk]
  exact hq

end show_case

def kurry (f : α × β × γ → δ) : (α → β → γ → δ) :=
  fun a b g => f (a, (b, g))

def curry : (α × β → γ) → α → β → γ :=
  fun f x y => f (x, y)

def uncurry : (α → β → γ) → α × β → γ :=
  fun f (x, y) => f x y

def flipp (f : α → β → γ) : β → α → γ :=
  fun b a => f a b

section test
variable {α β γ δ : Type}
#check (α × (β × γ)) → δ

def pog : (Nat × Int × Float) → Nat :=
  fun (m, _, _) => m

#check fun n => curry $ (curry pog) n
#check fun n => curry $ (curry pog) n
#check (kurry) (pog )
#check ((curry ∘ ·) ∘ curry) pog

def pogg : (Char × Nat × Int × Float) → Nat :=
  fun (_, m, _, _) => m

#check fun n => curry $ (curry pogg) n
#check fun (n, m) => curry $ (fun n => curry $ (curry pogg) n) n m
#check fun (n, m) => curry $ (fun n => curry $ (curry pogg) n) n m

#check (((curry ∘ ·) ∘ curry ∘ ·) ∘ curry) pogg
#check ((curry ∘ ·) ∘ curry) pog

#check absurd -- absurd.{v} {a : Prop} {b : Sort v} (h₁ : a) (h₂ : ¬a) : b

end test





-- (A × B × C → D) → A → B → C → D
#eval 3
#check 3
#check some 3
#check (none : Option Nat)

def tres_embalado := some 3
def codigo_cliente : Option Int := none

#check tres_embalado
#check codigo_cliente


def maybe_div2 (n : Nat) : Option Nat :=
  if n % 2 = 0 then
    some (n / 2)
  else
    none

-- pure : α → m α
-- bind : m α × (α → m β) → m β

#check (· + 2)

#eval ((pure  ∘ (· + 2)) 4 : Option Nat)

#eval maybe_div2 5
#eval bind (maybe_div2 20) maybe_div2
#eval (maybe_div2 56)
#eval bind (bind (maybe_div2 56) maybe_div2) maybe_div2
#eval bind (bind (bind (maybe_div2 112) maybe_div2) maybe_div2) maybe_div2
#eval maybe_div2 112 >>= maybe_div2
                     >>= maybe_div2

#eval maybe_div2 =<< maybe_div2 56

#eval maybe_div2 112 >>= maybe_div2
                     >>= pure ∘ (· + 2)
                     >>= pure ∘ (· * 2)
                     >>= maybe_div2
                     >>= maybe_div2


#eval maybe_div2 112 >>= maybe_div2
                     >>= maybe_div2 ∘ (· * 2) ∘ (· + 2)
                     >>= maybe_div2

#eval maybe_div2 112 >>= pure ∘ (· + 2)
                     >>= maybe_div2

#eval do {
  let x <- maybe_div2 112;
  let y <- maybe_div2 (x + 2);
  return y
}

-- def lesses (n : Nat) : List Nat :=
--   match n with
--   | 0     => []
--   | k + 1 => k :: lesses k

-- #eval lesses 5
-- #eval lesses 15

inductive Result

-- def rust : IO Nat := do {
--   let exit := return 0
--   let opt_x <- pure (maybe_div2 38)
--   match opt_x with
--   | none   => exit
--   | some x =>
--     let opt_y <- pure (maybe_div2 x)
--       match opt_y with
--       | none   => exit
--       | some y =>
--         let opt_z <- pure (maybe_div2 y)
--           match opt_z with
--           | none   => exit
--           | some z => pure z
-- }

-- #print rust

-- #eval rust


-- pure : α → m α
-- bind : m α → (α → m β) → m β
--

def Implies (p q : Prop) : Prop := p → q
  #check And     -- Prop → Prop → Prop
  #check Or      -- Prop → Prop → Prop
  #check Not     -- Prop → Prop
  #check Implies -- Prop → Prop → Prop

  variable (p q r : Prop)
  #check And p q                      -- Prop
  #check Or (And p q) r               -- Prop
  #check Implies (And p q) (And q p)  -- Prop
  #check Prop

variable (p q : Prop)

structure Proof (p : Prop) : Type where
  proof : p

#check Proof   -- Proof : Prop → Type

axiom and_commm (p q : Prop) : Proof (Implies (And p q) (And q p))

#check and_commm p q     -- Proof (Implies (And p q) (And q p))

axiom modus_ponens  : (p q : Prop) → Proof (Implies p q) → Proof p → Proof q
axiom implies_intro : (p q : Prop) → (Proof p → Proof q) → Proof (Implies p q)

#check Sort 0 → Sort 0
#check p → q
#check Nat
#check String
#check Nat → String
#check Sort 1

namespace working_with_propositions_as_types

variable {p q : Prop}

theorem t1_0 : p → q → p :=
  fun hp : p =>
    (fun hq : q =>
      hp)

theorem t1_1 : p → q → p :=
  fun hp : p =>
    fun _ => hp


def t1_2 : p → q → p :=
  fun hp : p =>
    fun _ => hp

#print t1_2
#print t1_1
#print t1_0

theorem t1_3 : p → q → p :=
  fun hp : p =>
  fun hq : q =>
  show p from hp

#print t1_3

theorem t1_4 (hp : p) (hq : q) : p := hp

axiom hp : p

theorem t2 : q → p := t1_4 hp

#print t1_4

axiom u       : Empty
axiom unsound : False

#check False
#eval  False
#print False
#print True

-- Everything follows from false (- in some worlds)

theorem ex : 1 = 0 :=
  False.elim unsound

#print ex


theorem t1_5 {p q : Prop} (hp : p) (hq : q) : p := hp

#print t1_5

theorem t1_6 : ∀ {p q : Prop}, p → q → p :=
  fun {p q : Prop} (hp : p) (hq : q) => hp

#print t1_6

def id_0 {α : Type} : α → α :=
  id

def id_1 : ∀ {α : Type}, α → α :=
  id

variable (hp : p)

theorem t1_7 : q → p :=
  fun _ =>
    show p from hp

#print t1_6
#check t1_6

section s1
  theorem t1 (p q : Prop) (hp : p) (hq : q) : p := hp

  variable (p q r s : Prop)

  #check t1 p q                -- p → q → p
  #check t1 r s                -- r → s → r
  #check t1 (r → s) (s → r)    -- (r → s) → (s → r) → r → s

  variable (h : r → s)
  #check t1 (r → s) (s → r) h  -- (s → r) → r → s
end s1

section s2
  variable (p q r s : Prop)

  theorem t2_0 (h₁ : q → r) (h₂ : p → q) : p → r :=
    fun hₚ : p =>
    show r from (h₁ ∘ h₂) hₚ
end s2


end working_with_propositions_as_types

namespace testing_more
variable (p q : Prop)

example (hp : p) (hq : q) : p ∧ q := And.intro hp hq

#check fun (hp : p) (hq : q) => And.intro hp hq

#check And.intro -- {a b : Prop} (left : a) (right : b) : a ∧ b
#check And.left  -- {a b : Prop} (self : a ∧ b) : a
#check And.right -- {a b : Prop} (self : a ∧ b) : b

example (h : p ∧ q) : q ∧ p :=
  show q ∧ p from ⟨h.right, h.left⟩

end testing_more

namespace disjuction
variable (p q : Prop)
example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq

#check Or.intro_left  -- {a : Prop} (b : Prop) (h : a) : a ∨ b
#check Or.intro_right -- {b : Prop} (a : Prop) (h : b) : a ∨ b
#check Or.elim        -- {a b c : Prop} (h : a ∨ b) (left : a → c) (right : b → c) : c
#check Or.inl         -- {a b : Prop} (h : a) : a ∨ b
#check Or.inr         -- {a b : Prop} (h : a) : a ∨ b



example (h : p ∨ q) : q ∨ p :=
  Or.elim h
    (fun hp : p =>
      show q ∨ p from Or.intro_right q hp)
    (fun hq : q =>
      show q ∨ p from Or.intro_left p hq)

example (h : p ∨ q) : q ∨ p :=
  h.elim (fun hp => Or.inr hp) (fun hq => Or.inl hq)

end disjuction

namespace negation
variable (p q : Prop)
example (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun hp : p =>
  show False from hnq (hpq hp)

example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)

#check False.elim -- False.elim.{u} {C : sort u} (h : False) : C

variable (p q r : Prop)

example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
  absurd (hqp hq) hnp

#check True.intro

end negation

namespace iff

variable {p q : Prop}
#check Iff.intro -- {a b : Prop} (mp : a → b) (mpr : b → a) : a ↔ b
def thing : p ↔ p := ⟨id , id⟩
#check Iff.intro -- {a b : Prop} (mp : a → b) (mpr : b → a) : a ↔ b
#check Iff.mp    -- {a b : Prop} (self : a ↔ b) : a → b
#check Iff.mpr   -- {a b : Prop} (self : a ↔ b) : b → a

variable (p q : Prop)

theorem and_swap : p ∧ q ↔ q ∧ p :=
  let f {r s : Prop} (h : r ∧ s) : s ∧ r := ⟨h.2, h.1⟩
  ⟨f, f⟩

example (h : p ∧ q) : q ∧ p := (and_swap p q).mp h

end iff

namespace subgoals
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from ⟨hq, hp⟩

example (h : p ∧ q) : q ∧ p :=
  let hp : p := h.left
  let hq : q := h.right
  show q ∧ p from ⟨hq, hp⟩

variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from And.intro hq hp
  show q from And.right h

end subgoals

namespace classical
open Classical

variable (p : Prop)

#check em              -- Classical.em (p : Prop) : p ∨ ¬p
#check byCases         -- {p q : Prop} (hpq : p → q) (¬p → q) : q
#check byContradiction -- {p : Prop} (h : ¬p → False) : p
#check Classical.em


theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)

end classical

namespace hw
  structure Point2D where
    x : Float
    y : Float
  deriving Repr

  def pred α := α → Prop

  def ex_un.{u} {α : Type u} (p : pred α) : Prop :=
    ∃ (a : α), p a ∧ ∀ (a' : α), p a' → a = a'

  #print ex_un

  def bin_prod_of.{u} (P α β : Type u) (p₁ : P → α) (p₂ : P → β) : Prop :=
    ∀ (C : Type u), ∀ (f : C → α), ∀ (g : C → β),
      ex_un (fun p : C → P => p₁∘ p = f ∧ p₂∘ p = g)


  theorem prod_Point2D : bin_prod_of Point2D Float Float Point2D.x Point2D.y := by
    rw [bin_prod_of]
    intros C f g
    rw [ex_un]
    exists (fun c : C => ⟨(f c), (g c)⟩)
    apply And.intro
    · -- Exists
      apply And.intro
      · -- first equality
        apply funext
        intro c
        simp
      · -- secc equality
        apply funext
        intro c
        simp
    · -- Unicity
      intro P'
      intro h
      rw [← h.left]
      rw [← h.right]
      simp

end hw
