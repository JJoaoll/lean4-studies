open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

#check Exists.elim

section test

notation h ".l" => And.left h
notation h ".r" => And.right h

variable {p q r s : Prop}
variable {hp : p} {hq : q} {hr : r} {hs : s}

#check (And.intro hp hq).l
#check (And.intro hp hq).r

end test

-- useless variable
example : (∃ x : α, r) → r :=
  fun h : ∃ _ : α, r =>
    Exists.elim h (fun _ : α => fun hx : r => hx)

example (a : α) : r → (∃ x : α, r) :=
  fun hr => ⟨a, hr⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
    (fun hx_pxr : ∃ x, p x ∧ r =>
      Exists.elim hx_pxr (fun w hw =>
       And.intro ⟨w, hw.left⟩ hw.right))
    (fun hxpx_r : (∃ x, p x) ∧ r =>
      Exists.elim hxpx_r.left (fun w hw =>
        Exists.intro w ⟨hw, hxpx_r.right⟩))

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (fun h₁ : ∃ x, p x ∨ q x =>
      match h₁ with
      | ⟨w, Or.inl hp⟩ => Or.inl ⟨w, hp⟩
      | ⟨w, Or.inr hq⟩ => Or.inr ⟨w, hq⟩)
    (fun h₂ : (∃ x, p x) ∨ (∃ x, q x) =>
      match h₂ with
      | Or.inl ⟨w, hp⟩ => ⟨w, Or.inl hp⟩
      | Or.inr ⟨w, hq⟩ => ⟨w, Or.inr hq⟩)

#check byCases
example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
  -- Constructive
    (fun hap : ∀ x, p x =>
      fun ⟨w, hnp⟩ =>
        have := hap w
        absurd this hnp)
  -- Heresy
    (fun hnp : ¬ (∃ x, ¬ p x) =>
      fun x : α => byCases
        (fun hpx  : p x => hpx)
        (fun hnpx : ¬ p x =>
          absurd ⟨x, hnpx⟩ hnp))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
   -- Strong
    (fun ⟨x, px⟩ =>
      fun hnp : ∀ x, ¬ p x =>
        absurd px (hnp x))
   -- WEAKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKK
    (fun hn_np : ¬ (∀ x, ¬ p x) => byCases -- by contradictions would be better
      (fun hk : ∃ x, p x => hk)
      (fun hnk : ¬ (∃ x, p x) =>
       suffices hnp : ∀ x, ¬ p x from absurd hnp hn_np
       fun x : α => byCases
         (fun hpx =>
           have := ⟨x, hpx⟩
           absurd this hnk)
         (fun hnpx => hnpx)))

-- Very constrictive
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
    (fun h₁ : ¬ ∃ x, p x =>
      fun x hpx =>
        suffices hn₁ : ∃ x, p x from absurd hn₁ h₁
        show ∃ x, p x from ⟨x, hpx⟩)
    (fun h₂ : ∀ x, ¬ p x =>
      fun ⟨x, hpx⟩ =>
        have := h₂ x
        absurd hpx this)

#check byContradiction
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro
    (fun h₁ : ¬ ∀ x, p x => byContradiction 
      fun hne : ¬ ∃ x, ¬ p x => 
        suffices hn₁ : ∀ x, p x from absurd hn₁ h₁ 
        fun x : α => byCases 
          (fun hpx  => hpx)
          (fun hnpx => 
            have := ⟨x, hnpx⟩ 
            absurd this hne))
    (fun ⟨x, hnpx⟩ => 
      fun hn₁ : ∀ x, p x => 
        have hpx := hn₁ x 
        absurd hpx hnpx)


example : (∀ x, p x → r) ↔ (∃ x, p x) → r := 
  Iff.intro
    (fun h : ∀ x, p x → r =>
      fun ⟨x, hpx⟩ =>
        have := h x
        have := this hpx
        show r from this)

    (fun h' : (∃ x, p x) → r =>
      fun (x : α) (hpx : p x) =>
        suffices hepx : ∃ x, p x from h' hepx
        show ∃ x, p x from ⟨x, hpx⟩)

-- Don't over think it :+1:
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (fun ⟨x, hpx_r⟩ =>
      fun hapx : ∀ x, p x =>
        have := hapx x
        have := hpx_r this
        show r from this)
    (fun h : (∀ x, p x) → r => sorry)


example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro
    (fun w : ∃ x, r → p x => fun hr : r =>
      match w with
      | ⟨x, h⟩ => Exists.intro x (h hr))
    (sorry)


#check Exists.intro --> Exists.intro.{u} {α : Sort u} {p : α → Prop} (w : α) (h : p w) : Exists p
#check Exists.elim  --> Exists.elim.{u} {α : Sort u} {p : α → Prop} {b : Prop} (h₁ : ∃ x, p x) (h₂ : ∀ (a : α), p a → b) : b



















-- some solutions:

-- open Classical

-- variable (α : Type) (p q : α → Prop)
-- variable (a : α)
-- variable (r : Prop)

-- example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
--   Iff.intro
--     (fun ⟨a, (h1 : p a ∨ q a)⟩ =>
--       Or.elim h1
--         (fun hpa : p a => Or.inl ⟨a, hpa⟩)
--         (fun hqa : q a => Or.inr ⟨a, hqa⟩))
--     (fun h : (∃ x, p x) ∨ (∃ x, q x) =>
--       Or.elim h
--         (fun ⟨a, hpa⟩ => ⟨a, (Or.inl hpa)⟩)
--         (fun ⟨a, hqa⟩ => ⟨a, (Or.inr hqa)⟩))

-- example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
--   Iff.intro
--     (fun ⟨b, (hb : p b → r)⟩ =>
--      fun h2 : ∀ x, p x =>
--      show r from hb (h2 b))
--     (fun h1 : (∀ x, p x) → r =>
--      show ∃ x, p x → r from
--        byCases
--          (fun hap : ∀ x, p x => ⟨a, λ h' => h1 hap⟩)
--          (fun hnap : ¬ ∀ x, p x =>
--           byContradiction
--             (fun hnex : ¬ ∃ x, p x → r =>
--               have hap : ∀ x, p x :=
--                 fun x =>
--                 byContradiction
--                   (fun hnp : ¬ p x =>
--                     have hex : ∃ x, p x → r := ⟨x, (fun hp => absurd hp hnp)⟩
--                     show False from hnex hex)
--               show False from hnap hap)))
