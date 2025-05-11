
universe u
-- variable (α : Type u)
-- O foco INICIAL aqui não vai ser a escrita (nomes, etc), mas ter a transcrição do material v1.
-- notation:1000 a " < " f:10000 " > " b => f ⟨a, b⟩

class Z1 (Int : Type u) where
  zero : Int
  one  : Int
  add  : Int × Int → Int
  minus: Int → Int
  mul  : Int × Int → Int

  ZA_Ass : ∀ (a b c : Int), add (a, add (b, c)) = add (add (a, b), c)
  ZA_IdR : ∀ (a : Int), add (a, zero) = a
  ZA_InvR: ∀ (a : Int), add (a, minus a) = zero
  ZA_Com : ∀ (a : Int), add (a, b) = add (b, a)

  ZM_Ass : ∀ (a b c : Int), mul (a, mul (b, c)) = mul (mul (a, b), c)
  ZM_IdR : ∀ (a : Int), mul (a, one) = a
  ZM_Com : ∀ (a : Int), mul (a, b) = mul (b, a)

  Z_DistR : ∀ (d a b : Int), mul (add (a, b), d) = add (mul (a, d), mul (b, d))

-- open Z1
-- TODO: melhorar notações pra implementar coisas e também pra definir as associatividades.
-- O bom de não definir as ass é não precisar do pp.parens true.
instance [Z1 α] : Add α where
  add := fun x y => Z1.add (x, y)

instance [Z1 α] : Neg α where
  neg := Z1.minus


-- notation:50 a " + " b => Z1.add ⟨a, b⟩
-- notation:70 "-"a      => Z1.minus a
notation:60 a " · " b => Z1.mul ⟨a, b⟩

section whos_left
open Z1

theorem ZA_IdL  [Z1 α]: ∀ (a : α), add (zero, a) = a := by
  intro a
  calc
    add (zero, a)
    _ = add (a, zero) := by rw [ZA_Com]
    _ = a             := by rw [ZA_IdR]

theorem ZA_InvL [Z1 Z]: ∀ (a : Z), add (minus a, a) = zero := by
  intro a
  calc
    add (minus a, a)
    _ = add (a, minus a) := by apply ZA_Com
    _ = zero             := by apply ZA_InvR


theorem ZM_IdL [Z1 α]: ∀ (a : α), mul (one, a) = a := by
  intro a
  calc
    mul (one, a)
    _ = mul (a, one) := by apply ZM_Com
    _= a             := by apply ZM_IdR

theorem Z_DistL [Z1 α]: ∀ (d a b : α), mul (d, add (a, b)) = add (mul (d, a), mul (d, b)) := by
  intros d a b
  calc
    mul (d, add (a, b))
    _ = mul (add (a, b), d)          := by apply ZM_Com
    _ = add (mul (a, d), mul (b, d)) := by apply Z_DistR
    _ = add (mul (d, a), mul (d, b)) := by rw [ZM_Com a, ZM_Com b]

end whos_left

section passar_pro_outro_lado
open Z1

theorem noname1 [Z1 Z]: ∀ (a b c : Z), add (a, b) = c ↔ a = add (c, minus b) := by
  intros a b c
  constructor <;> intro h -- better way?
  have :=
    calc
      add (c, minus b)
      _ = add (add (a, b), minus b) := by rw [h]
      _ = add (a, add (b, minus b)) := by rw [ZA_Ass]
      _ = add (a, zero)             := by rw [ZA_InvR]
      _ = a                         := by rw [ZA_IdR]
  rw [this]
  calc
    add (a, b)
    _ = add (add (c, minus b), b) := by rw [h]
    _ = add (c, add (minus b, b)) := by rw [ZA_Ass]
    _ = add (c, zero)             := by rw [ZA_InvL]
    _ = c                         := by rw [ZA_IdR]

theorem noname2 [Z1 Int]: ∀ (a b c : Int), add (a, b) = c ↔ a = add (b, minus a) := by sorry
theorem noname3 [Z1 Int]: ∀ (a b : Int), a = b ↔  add (a, minus b) = zero := by sorry

end passar_pro_outro_lado

-- heart thing
section outras
open Z1

theorem ZA_CanR [Z1 Int]: ∀ (a b c : Int), add (a, c) = add (b, c) → a = b := by sorry
theorem ZA_CanL [Z1 Int]: ∀ (a b c : Int), add (c, a) = add (c, b) → a = b := by sorry
-- refute os ZM_Can(L,R)

-- TODO: melhor o existe
--unicidade (+)-id
def Ex! (p : α → Prop) := (∃ x, p x) ∧ (∀ u v, p u ∧ p v → u = v)
-- notation "∃! " x " :  " p x  =>
def is_idL_of (e : α) (f : α × α → α) : Prop := ∀ a : α, f (e, a) = a
def is_idR_of (e : α) (f : α × α → α) : Prop := ∀ a : α, f (a, e) = a
def is_id_of (e : α) (f : α × α → α)  : Prop := (is_idL_of e f) ∧ (is_idR_of e f)


#check ZA_IdL
-- notation "∃!" x " : " type ", " p x => (∃ (x : type), p x) ∧ (∀ (u v : type), p u ∧ p v → u = v)
theorem ZA_id! [Z1 α] : ∃ x : α, is_id_of x Z1.add := by
  exists zero
  apply And.intro <;> intro a
  · rw [ZA_IdL]
  · rw [ZA_IdR]


-- unicidade (·)-id
theorem ZM_Id! [Z1 α] : ∃ x : α, is_id_of x Z1.mul := by
  exists one
  apply And.intro <;> intro a
  · rw [ZM_IdL]
  · rw [ZM_IdR]

-- unicidade inversos-aditivos
theorem ZA_Inv! [Z1 α] 
-- unicidade de resoluçòes (p. 70)
-- ~~unicidades anteriores como corolario das resoluicoes unicas?~~
-- neg inv: --x = x
-- -1a = -a
-- -ab = -(ab) = a(-b)
-- (-a)(-b) = ab
-- -(a - b) = b - a ∧ - (a + b) = -a - b.
--
--
--
--
-- lean style:
-- Z_AnnL/zero_mul_zero
-- Z_AnnR/mul_zero_zero
--

end outras

class Z2 (Int : Type u) extends Z1 Int where
  Z_NZD : ∀ (a b : Int), mul (a, b) = zero → a = zero ∨ b = zero

notation:50 a " - " b => a + -b
