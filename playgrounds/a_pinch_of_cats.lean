namespace few_cats

#check Type
#check (· → ·)
#check Type → Type → Type

-- universe u
-- variable {α β γ : Type u}
-- def Obj.{u} {α : Type u} : Type u := α
-- def Arr.{u} {α : Type u} : Type u := α → α → Type v

-- class Cat.{u} (Obj : Type u) where
--   Arr : Obj → Obj → Type v


class Cat.{u} (Obj : Type u) where
  Arr : Obj → Obj → Type v

  -- heros:
  id   : (A : Obj) → Arr A A
  comp : {A B C : Obj} → Arr B C → Arr A B → Arr A C

  -- laws:
  id_law  : ∀ {A B : Obj}, ∀ (f : Arr A B), comp (id B) f = f ∧
                          ∀ (g : Arr A B), comp g (id A) = g
  ass_law : ∀ {A B C D : Obj} (f : Arr C D) (g : Arr B C) (h : Arr A B),
    comp f (comp g h) = comp (comp f g) h
open Cat

def src.{u} {C : Type u} [Cat C] {A B : C} (_ : Arr A B) : C := A
def tgt.{u} {C : Type u} [Cat C] {A B : C} (_ : Arr A B) : C := B

notation "𝟙" => Cat.id
infixr:80 " ∘ " => Cat.comp

class Functor (C : Type u) [Cat C] (D : Type w) [Cat D] where
  map_obj  : C → D
  map_arr  : {A B : C} → Arr A B → Arr (map_obj A) (map_obj B)
  map_id   : {A : C} → map_arr (𝟙 A) = 𝟙 (map_obj A)
  map_comp : {A B C : C} → (g : Arr B C) → (f : Arr A B) → map_arr (g ∘ f) = map_arr g ∘ map_arr f

  -- src_law : ∀ {A B : C}, src ∘ map_arr = (map_obj ∘ src)




notation F "⋅" x => Functor.obj F x notation F "∘" f => Functor.map F f





end few_cats
