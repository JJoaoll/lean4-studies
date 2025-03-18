-- simplified monad class:
-- class Monad (m : Type → Type) where
--   pure : α → m α
--   bind : m α → (α → m β) → m β

instance : Monad Option where
  pure x := some x
  bind opt next :=
    match opt with
    | none   => none
    | some x => next x

instance : Monad (Except ε) where
  pure x := Except.ok x
  bind attempt next :=
    match attempt with
    | Except.error e => Except.error e
    | Except.ok x    => next x

-- examples:


def pred : Nat → Option Nat
  | 0     => none
  | n + 1 => some n

#eval pred 1
#eval bind (pred 1) pred
#eval bind (pred 2) pred
#eval pred =<< pred 2
#eval pred 3 >>= pred >>= pred >>= pred

def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs =>
    f x >>= fun hd =>
    mapM f xs >>= fun tl =>
    pure (hd :: tl)

#eval mapM pred [1, 2, 3, 4, 5]
#eval mapM pred [0, 1, 2, 3, 4, 5]

def State (σ : Type) (α : Type) : Type :=
  σ → (σ × α)

def ok (x : α) : State σ α :=
  fun s => (s, x)

def get : State σ σ :=
  fun s => (s, s)

def set (s : σ) : State σ Unit :=
  fun _ => (s, ())

#eval ok 3 "erro?"
#eval ok "ro" 3

#eval get $ ok 3 "erro?"
