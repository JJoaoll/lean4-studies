-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro
  repeat (first | constructor | intro h | assumption | cases h)

example : p ∨ q ↔ q ∨ p := by
  apply Iff.intro
  all_goals (intro hpq; apply Or.elim hpq;)
  all_goals (repeat (first | intro h | exact Or.inr h | exact Or.inl h))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  apply Iff.intro
  all_goals (intro h; constructor; cases h;)
  any_goals constructor;
  any_goals (rename_i left right; first | cases left | cases right)
  all_goals admit

-- it could be shorther?
open Or in
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  apply Iff.intro
  · intro h
    cases h with
    | inl h' =>
      cases h' with
      | inl hp => exact inl hp
      | inr hq => exact inr (inl hq)
    | inr hr => exact inr (inr hr)
  · intro h
    cases h with
    | inr h' =>
      cases h' with
      | inr hr => exact inr hr
      | inl hq => exact inl (inr hq)
    | inl hp => exact inl (inl hp)

-- distributvity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  · intro ⟨_, hqₒr⟩
    cases hqₒr with
    | inl hq => apply Or.inl; constructor <;> assumption;
    | inr hr => apply Or.inr; constructor <;> assumption;

  · intro hpqₒpr
    cases hpqₒpr with
    | inl hpq => cases hpq; constructor; repeat (first | assumption | apply Or.inl)
    | inr hpr => cases hpr; constructor; repeat (first | assumption | apply Or.inr)

-- Yup, i could use the pairing function and just type things like
-- ⟨f, g⟩
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  · intro h
    cases h with
    | inl _ => constructor; repeat (first | apply Or.inl | assumption)
    | inr hqr => cases hqr; constructor; repeat (first | apply Or.inr | assumption)
  · intro ⟨hpq, hpr⟩
    cases hpq with
    | inl hp => apply Or.inl; assumption;
    | inr hq =>
      cases hpr with
      | inl hp => apply Or.inl; assumption;
      | inr hr => apply Or.inr; constructor <;> assumption;


def uncurry.{u} {α β γ : Type u} : (α → (β → γ)) → (α × β → γ) := by
  intro f ⟨a, b⟩
  apply f <;> assumption

def curry.{u} {α β γ : Type u} : (α × β → γ) → (α → (β → γ)) := by
  intro f a b
  suffices axb : α × β from f axb
  constructor <;> assumption

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  apply Iff.intro
  -- (=>)
  · intro f ⟨hp, hq⟩
    apply f <;> assumption

  -- (<=)
  · intro f hp hq
    suffices hpxhq : p ∧ q from f hpxhq
    constructor <;> assumption

-- it could be smaller but..
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  apply Iff.intro
  · intro h
    constructor;
    repeat (first | intro h' | exact h $ Or.inl h' | exact h $ Or.inr h')

  · intro ⟨hp_r, hq_r⟩ hpₒq
    cases hpₒq
    repeat (first | apply hp_r ; assumption | apply hq_r ; assumption)

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  apply Iff.intro
  · intro hnpₒq
    constructor <;> intro h <;> apply hnpₒq
    repeat (first | apply Or.inl ; assumption | apply Or.inr ; assumption)


  · intro ⟨hnp, hnq⟩ hpₒq
    cases hpₒq <;> (first | apply hnp ; assumption | apply hnq ; assumption)

example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro h ⟨_, _⟩
  cases h <;> contradiction


example : ¬(p ∧ ¬p) := by
  intro ⟨_, _⟩
  contradiction

example : p ∧ ¬q → ¬(p → q) := by
  intro ⟨hp, _⟩ hp_q
  have := hp_q hp
  contradiction

#check False.elim
example : ¬p → (p → q) := by
  intros
  contradiction

-- isso acaba sendo uma funcao vazia?
-- parece uma forma de dizer que o p eh inicial..
example : (¬p ∨ q) → (p → q) := by
  intro h hp
  cases h
  · contradiction;
  · assumption;

example : p ∨ False ↔ p := by
  apply Iff.intro
  all_goals intro h
  · cases h <;> (first | assumption | contradiction)
  · exact Or.inl h

example : p ∧ False ↔ False := by
  apply Iff.intro <;> intro h ; cases h
  · contradiction
  · constructor <;> contradiction

-- have hq := hp_q hp -- let or have?
example : (p → q) → (¬q → ¬p) := by
  intro hp_q hnq hp
  suffices hq : q from absurd hq hnq
  suffices hp : p from hp_q hp
  assumption

open Classical
variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro hp_pₒr
  cases em p
  · case inl hp =>
    cases hp_pₒr hp
    · apply Or.inl ; intros ; assumption
    · apply Or.inr ; intros ; assumption
  · apply Or.inl ; intros ; contradiction
  
-- not and -> or not not
example : ¬(p ∧ q) → ¬p ∨ ¬q := by 
  intro hn_pq 
  apply byContradiction
  intro hn_npₒnq
  cases em p <;> cases em q
  · have _ : p ∧ q := by
      constructor <;> assumption
    contradiction 
  all_goals have _ : ¬p ∨ ¬q := by 
    { first | apply Or.inl ; assumption
            | apply Or.inr ; assumption }

  all_goals contradiction

#check Not.imp
-- i really dont care to much about it in a not
-- interactive way, omaga, look at that!
-- but if it was a easiest way, i would like to know
example : ¬(p → q) → p ∧ ¬q := by 
  intros 
  constructor <;> by_cases p <;> by_cases q
  any_goals assumption
  all_goals suffices hp_q : p → q by contradiction 
  all_goals intros 
  repeat (first | assumption | contradiction)

  /- constructor <;> by_cases p <;> by_cases q -/
  /- all_goals intros -/
  /- any_goals (first | assumption | contradiction) -/

#check byCases

example : (p → q) → (¬p ∨ q) := by 
  intro hp_q 
  by_cases p 
  · apply Or.inr
    apply hp_q 
    assumption
  · apply Or.inl
    assumption 

#check byContradiction
-- whats ur name, theorem? if i knewd would be awesome ;-;
-- Loogle when?
example : (¬q → ¬p) → (p → q) := by 
  intro h hp 
  by_cases q 
  · assumption 
  · exfalso 
    suffices hnp : ¬p by contradiction
    apply h 
    assumption 

example : p ∨ ¬p := by 
  exact em p 

example : (((p → q) → p) → p) := by 
  intro h 
  apply byContradiction
  intro hnp
  suffices hp : p by contradiction
  apply h 
  intros ; contradiction

-- (i : I) ⊢ A :(i)
-- syntax "QED" : tactic

-- macro_rules
--   | `(tactic| QED) => `(tactic| assumption)

-- variable (p q r : Prop)

-- example (hp : p) : p := by
--   QED;
