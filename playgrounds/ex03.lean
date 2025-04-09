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




-- not and -> or not not
example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  fun hn_pq   =>
    let hp_np := em p
    Or.elim hp_np
    (fun hp  =>
      suffices hnq : ¬q from Or.inr hnq
      (fun hq =>
        let hpq := And.intro hp hq
        absurd hpq hn_pq))
    (fun hnp => Or.inl hnp)

#check Not.imp
-- i really dont care to much about it in a not
-- interactive way, omaga, look at that!
-- but if it was a easiest way, i would like to know
example : ¬(p → q) → p ∧ ¬q :=
  fun hn_ptoq =>
    let hp_np := em p
    let hq_nq := em q
    have f : (¬q → ¬p) → (p → q) :=
      fun hnq_np hp =>
        Or.elim hq_nq
        (fun hq => hq)
        (fun hnq =>
          absurd hp (hnq_np hnq))
    Or.elim hq_nq
      (fun hq => absurd (fun _ => hq) (hn_ptoq))
      (fun hnq =>
        Or.elim hp_np
        (fun hp => ⟨hp, hnq⟩)
        (fun hnp =>
          suffices hp_q : p → q from absurd hp_q hn_ptoq
          suffices hnq_np : ¬q → ¬p from f hnq_np
          show ¬q → ¬p from fun _ => hnp))

#check byCases
example : (p → q) → (¬p ∨ q) :=
  fun hp_q => byCases
    (fun hp  :  p => Or.inr $ hp_q hp)
    (fun hnp : ¬p => Or.inl hnp)

#check byContradiction
-- whats ur name, theorem? if i knewd would be awesome ;-;
-- Loogle when?
example : (¬q → ¬p) → (p → q) :=
  fun hnq_np hp => byContradiction
   (fun hnq =>
     let hnp := hnq_np hnq
     absurd hp hnp)

example : p ∨ ¬p := em p
example : (((p → q) → p) → p) :=
  fun hpk => byCases
    (fun hp  :  p => hp)
    (fun hnp : ¬p =>
      suffices hp_q : p → q from hpk hp_q
      fun hp => absurd hp hnp)



-- syntax "QED" : tactic

-- macro_rules
--   | `(tactic| QED) => `(tactic| assumption)

-- variable (p q r : Prop)

-- example (hp : p) : p := by
--   QED;
