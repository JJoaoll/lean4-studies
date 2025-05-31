
-- Definições iniciais:
---------------------------------------------------------------------------
def inverses (f : α → β) (g : β → α) := g ∘ f = @id α ∧ f ∘ g = @id β
def invertible (f : α → β) := ∃ g : β → α, inverses f g
def Type.iso.{u, v} (α : Type u) (β : Type v) := ∃ f : α → β, invertible f

infixl:100 " ≅ " => Type.iso

def nonEmpty.{u} (α : Type u) := ∃ x : α, True
def isEmpty.{u} (α : Type u) := ∀ x : α, False

def voidFun™ : Empty → Empty
  | e => nomatch e

#check voidFun™
---------------------------------------------------------------------------
-- Teoremas-->>

theorem voidFun™_iso_unity : (Empty → Empty) ≅ Unit := by
  let f : (Empty → Empty) → Unit :=
    fun _ => ()
  let g : Unit → (Empty → Empty) :=
    fun _ e => nomatch e

  exists f
  exists g
  apply And.intro
  · funext (_ : Empty → Empty) (e : Empty)
    exact Empty.elim e
  · funext (u : Unit)
    calc
      (f ∘ g) u
      _ = f (g u) := by rw [Function.comp]
      _ = u       := by rfl -- rw [g] (f e g são sintáticas)

#print voidFun™_iso_unity

theorem voidFun™_unicity : ∀ f g : Empty → Empty, f = g := by
  intros f g
  funext (e : Empty)
  exact e.elim

#print voidFun™_unicity


---------------------------------------------------------------------------
-- Demonstramos isso sem tanto trabalho, no entanto, daria pra matar esses
-- casos com algo mais geral.

def voidFun.{u} {α : Type u} : Empty → α
  | e => nomatch e

-- Note que apenas mudando os tipos, tudo já compila :P.
theorem voidFun_iso_unity.{u} {α : Type u} : (Empty → α) ≅ Unit := by {
  let f : (Empty → α) → Unit :=
    fun _ => ()
  let g : Unit → (Empty → α) :=
    fun _ e => nomatch e

  exists f
  exists g
  apply And.intro
  · funext (_ : Empty → α) (e : Empty)
    exact Empty.elim e
  · funext (u : Unit)
    calc
      (f ∘ g) u
      _ = f (g u) := by rw [Function.comp]
      _ = u       := by rfl -- rw [g] (f e g são sintáticas)
}

-- com isso, ganhamos a outra de brinde!
example : (Empty → Empty) ≅ Unit := by
  apply @voidFun_iso_unity Empty

-- de maneira similar, poderíamos ter feito:
theorem voidFun_unicity.{u} {α : Type u} : ∀ f g : Empty → α, f = g := by
  intros f g
  funext (e : Empty)
  exact e.elim
-- novamente apenas mudamos os tipos.

-- Agora coletamos o que ficou de graça :P
example : ∀ f g : Empty → Empty, f = g := by
  apply @voidFun_unicity Empty
---------------------------------------------------------------------------
-- p/ essa parte cairemos na classicidade, mas acaba não sendo um problema :P

-- A lean separa a Empty da False, então talvez isso fique estranho..
theorem empty_unicity.{u} : ∀ α : Type u, isEmpty α → α ≅ Empty := by
  intros α hα
  have f : α → Empty := by
    intro x
    exact False.elim (hα x)
  have g : Empty → α := by
    intro e
    exact Empty.elim e

  exists f
  exists g
  apply And.intro

  · funext x
    exact Empty.elim (f x)
  · funext e
    exact Empty.elim e

-- nomes estranhos foram escolhidos.
theorem empty_no_nonEmpty.{u} : ∀ α : Type u, isEmpty α ↔ ¬(nonEmpty α) := by
  intro α
  apply Iff.intro
  · intro hnα
    intro hα
    rcases hα with ⟨x, _⟩
    exact (hnα x).elim

  · intro hnα
    intro (x : α)
    apply hnα
    exists x

#print empty_no_nonEmpty

-- Com tudo isso, finalmente podemos usar o sistema proposicional
-- já pronto na Lean p/ demonstrar:
notation "~" p => p → Empty
theorem neg_effect.{u} : ∀ α : Type u, (~α) ≅ Empty ∨ (~α) ≅ Unit := by
  intro α
  by_cases he : isEmpty α
  · apply Or.inr  -- daria p/ mostrar q isEmpty funfa e trazer bijects daí.

    have f : (α → Empty) → Unit :=
      fun _ => ()
    have g : Unit → (α → Empty) :=
      fun _ x => (he x).elim

    exists f
    exists g
    apply And.intro
    · funext _ x
      apply (he x).elim

    · funext u
      calc
        (f ∘ g) u
        _ = f (g u) := by simp
        _ = ()      := by rfl -- rw [f]
        _ = id ()   := by rw [id]

  · apply Or.inl
    -- LEM moment:
    have : nonEmpty α := by
      have := mt (empty_no_nonEmpty α).2

      apply (@Classical.not_not $ nonEmpty α).1
      apply this
      apply he

    rcases this with ⟨x, _⟩

    have f : (α → Empty) → Empty
      | h => nomatch h x

    have g : Empty → (α → Empty)
      | e => nomatch e

    exists f
    exists g

    apply And.intro
    · funext h
      exact (h x).elim

    · funext e
      exact e.elim

-- Cansei, bora pro que interessa:
#check Unit.ext

def booleanismo.{u} : (p : Type u) → (hp hp' : ~~p) → hp = hp' := by
  intro p
  intro hp _
  funext hk
  exact (hp hk).elim

#print congr
