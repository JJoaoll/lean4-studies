example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun z : α =>
  show p z from (h z).left

section trans 
variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ x y z, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r    -- ∀ (x y z : α), r x y → r y z → r x z
#check trans_r a b c -- r a b → r b c → r a c
#check trans_r a b c hab -- r b c → r a c
#check trans_r a b c hab hbc -- r a c


end trans

section er 

variable (α : Type) (r : α → α → Prop)

variable (refl_r : ∀ x : α, r x x)
variable (symm_r : ∀ {x y : α}, r x y → r y x)
variable (trans_r : ∀ {x y z : α}, r x y → r y z → r x z)

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  trans_r (trans_r hab (symm_r hcb)) hcd

end er

variable (α : Type)
variable (p : ∀ α : Type u, Type u → Prop)

#check p p p 
#check test 
#check ∀test : α → Prop, True
#check Nat → Prop
#check Prop → Prop
#check Sort 0
#check List
#check Nat
#check List Nat




