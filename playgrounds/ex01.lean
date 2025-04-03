variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  let swap {p q : Prop} (h : p ∧ q) : q ∧ p := ⟨h.2, h.1⟩
  ⟨swap, swap⟩

open Or in
example : p ∨ q ↔ q ∨ p :=
  let change {p q : Prop} (h : p ∨ q) : q ∨ p := elim h inr inl
  ⟨change, change⟩

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun h => ⟨h.1.1, ⟨h.1.2, h.2⟩⟩)
    (fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩)


open Or in
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun h => elim h
      (fun h' => elim h' inl (inr ∘ inl))
      (inr ∘ inr))
    (fun h => elim h
      (inl ∘ inl)
      (fun h' => elim h' (inl ∘ inr) inr))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h => Or.elim h.2
      (fun hq => Or.inl ⟨h.1, hq⟩)
      (fun hr => Or.inr ⟨h.1, hr⟩))
    (fun h => Or.elim h
      (fun hpq => ⟨hpq.1, Or.inl hpq.2⟩)
      (fun hpr => ⟨hpr.1, Or.inr hpr.2⟩))

-- Yup, i could use the pairing function and just type things like
-- ⟨f, g⟩
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (fun h => Or.elim h
      (fun hp  => ⟨Or.inl hp, Or.inl hp⟩)
      (fun hqr => ⟨Or.inr hqr.1, Or.inr hqr.2⟩))
    (fun h => Or.elim h.1
      (fun hp   => Or.inl hp)
      (fun hq   => Or.elim h.2
        (fun hp => Or.inl hp)
        (fun hr => Or.inr ⟨hq, hr⟩)))

def uncurry.{u} {α β γ : Type u} : (α → (β → γ)) → (α × β → γ)
  | f, w => f w.1 w.2

def curry.{u} {α β γ : Type u} : (α × β → γ) → (α → (β → γ))
  | f, a, b => f (a, b)

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun f => fun hpq   => f hpq.1 hpq.2)
    (fun f => fun hp hq => f ⟨hp, hq⟩)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun h => And.intro
      (fun hp => h $ Or.inl hp )
      (fun hq => h $ Or.inr hq))
    (fun h => fun hpoq => Or.elim hpoq
      (fun hp => h.1 hp)
      (fun hq => h.2 hq))

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun hn_poq => And.intro
      (fun hp => hn_poq $ Or.inl hp)
      (fun hq => hn_poq $ Or.inr hq))
    (fun hnp_nq => fun hpₒq => Or.elim hpₒq
      (fun hp => absurd hp hnp_nq.1)
      (fun hq => absurd hq hnp_nq.2))

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun hnp_nq => Or.elim hnp_nq
    (fun hnp => fun hpq => absurd hpq.1 hnp)
    (fun hnq => fun hpq => absurd hpq.2 hnq)

example : ¬(p ∧ ¬p) :=
  fun hn_p_np =>
    have hp  := hn_p_np.1
    have hnp := hn_p_np.2
    absurd hp hnp

example : p ∧ ¬q → ¬(p → q) :=
  fun hp_nq =>
    have hp  := hp_nq.left
    have hnq := hp_nq.right
    fun hp_q =>
      suffices hq : q from absurd hq hnq
      show q from hp_q hp

#check False.elim
example : ¬p → (p → q) :=
  fun hnp hp => absurd hp hnp

example : (¬p ∨ q) → (p → q) :=
  fun hnp_q hp => Or.elim hnp_q
    (fun hnp => absurd hp hnp)
    (fun hq  => hq)

example : p ∨ False ↔ p :=
  Iff.intro
  (fun h => Or.elim h
    (fun hp => hp)
    (fun hf => False.elim hf))
  (Or.inl)

example : p ∧ False ↔ False :=
  Iff.intro
    (And.right)
    (False.elim)

-- have hq := hp_q hp -- let or have?
example : (p → q) → (¬q → ¬p) :=
  fun hp_q hnq hp =>
    let hq := hp_q hp -- let or have? well i have let or should i let have
    absurd hq hnq

open Classical
variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  fun hp_qₒr : p → q ∨ r =>
    let hp_np := em p
    Or.elim hp_np
      (fun hp =>
        let hqₒr := hp_qₒr hp
        Or.elim hqₒr
          (fun hq => Or.inl (fun _ => hq))
          (fun hr => Or.inr (fun _ => hr)))
      (fun hnp =>
        suffices hp_q : p → q from Or.inl hp_q
        fun hp => absurd hp hnp)

-- not and -> or not not
example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  fun hn_pq =>
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

example : (p → q) → (¬p ∨ q) := sorry
example : (¬q → ¬p) → (p → q) := sorry
example : p ∨ ¬p := sorry
example : (((p → q) → p) → p) := sorry
