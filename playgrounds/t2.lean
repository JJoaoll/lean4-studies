-- [1, 2, 3, 4]
-- [5, 6, 7, 8]

--     1  2  3  4
-- 5  [6, 7, 8, 9]
-- 6  [7, ...]
-- 7  []
-- 8  []

section s1
  open List

  universe u
  variable {α β γ : Type u}

  def zip_matrix_with (op : α → β → γ) : List α → List β → List (List γ)
    | []     , _  => []
    | a :: as, bs => map (op a) bs :: zip_matrix_with op as bs

  def count_matrix : List (List α) → Nat :=
    sum ∘ map length

  #eval zip_matrix_with (· ++ " " ++ ·) ["oi", "tchau"] ["mundo", "vida"]
  #eval zip_matrix_with (· + ·) [1, 2, 3, 4] [6, 7, 8, 9]
  #eval zip_matrix_with (·, ·) [1, 2, 3, 4] [6, 7, 8, 9]

  #check length
  #eval count_matrix $ zip_matrix_with (· + ·) [1, 2, 3, 4] [6, 7, 8, 9]
  #eval count_matrix $ zip_matrix_with (·, ·) [1, 2, 3, 4] [6, 7, 8, 9]

  theorem T1 : ∀(xs : List α), ∀(ys : List β), ∀(op : α → β → γ),
   count_matrix (zip_matrix_with op xs ys) = xs.length * ys.length := by

  intros xs ys
  intro op
  induction xs with
    | nil =>
      rw [zip_matrix_with]
      simp
      rw [count_matrix]
      simp

    | cons x xs' hi =>
      -- simp [zip_matrix_with, count_matrix, hi]
      rw [length]
      rw [Nat.succ_mul]
      rw [<- hi]
      rw [zip_matrix_with]
      rw [count_matrix]
      simp
      rw [Nat.add_comm]

  #check get?
  #check bind

  def l₁ := [1, 2, 3, 4, 5]
  def l₂ := [9, 8, 7, 6, 5]

  def m := zip_matrix_with (·, ·) l₁ l₂
  
  #eval m
  #eval get? m 0
  #check get? m 0
end s1

open List (get?)

#eval m
#eval get? m 0
#check get? m 0
#check bind (get? m 0)
#check (get? m 0) >>= (flip get? 0)
#check flip get?
#check m.get? 0
-- m a := Option <List natxnat>
-- a -> m b := List <nat x nat> -> Optional <nat x nat>

#check ((get? l₁ 0), (get? l₂ 0))

def no_name : (Option α × Option β) → Option (α × β)
  | (some a, some b) => some (a, b)
  | _ => none

def uncurry : (α → β → γ) → (α × β → γ)
  | f, (a, b) => f a b

#check no_name ((get? l₁ 0), (get? l₂ 0))

theorem correctness : ∀(xs : List α), ∀(ys : List β), ∀(op : α → β → γ), ∀(n m : Nat),
  -- ∀(n m : Nat), n < xs.length ∧ m < ys.length →
  (get? (zip_matrix_with op xs ys) n) >>= (flip get? m)
    = no_name ((get? xs n), (get? ys m)) >>= some ∘ uncurry op := by

  intros xs ys op
  intros n m
  sorry


def x     := 3 + 4 + 5
def f x y := x + y + 4

#check f

#check Prop

#check "oi"
#check String
#check Type

def endoF (α : Type) : Type :=
  α → α

def idd : endoF Nat
  | n => n
