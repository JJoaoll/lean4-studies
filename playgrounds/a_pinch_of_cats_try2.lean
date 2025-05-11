namespace FewCats
universe u v


-- notation "∀ (" f:20 " : " A " → " B " )" => ({f : Arr // A })
def typeOf (α : Type u) := Type u

class Cat (Obj : Type u) (Arr : Type v) where
  src : Arr → Obj
  tgt : Arr → Obj

  id : (A : Obj) → {idA : Arr // src idA = A ∧
                                 tgt idA = A }

  comp : {A B C : Obj}
    → {g : Arr // src g = B ∧ tgt g = C}
    → {f : Arr // src f = A ∧ tgt f = B}
    → {gof : Arr // src gof = A ∧ tgt gof = C}

  -- f : A → B, f ∘ id = f ∧ id ∘ f = f
  id_law : ∀ (A B : Obj), ∀ (f : {f' : Arr // src f' = A ∧ tgt f' = B}),
         comp f (id A) = f ∧ comp (id B) f = f

  assoc_law : ∀ (A B C D : Obj),
         ∀ (f : {f' : Arr // src f' = A ∧ tgt f' = B}),
         ∀ (g : {g' : Arr // src g' = B ∧ tgt g' = C}),
         ∀ (h : {h' : Arr // src h' = C ∧ tgt h' = D}),
         comp h (comp g f) = comp (comp h g) f


notation f " : " A " ─> " B => (f : {f' : Cat.Arr // Cat.src f' = A ∧ Cat.tgt f' = B})

class FunkCov ()

end FewCats
