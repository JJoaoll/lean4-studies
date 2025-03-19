
-- class Monad (m : Type → Type) where
--   pure : α → m α
--   bind : m α → (α → m β) → m β

inductive BinTree α where
| leaf   : BinTree α
| branch : BinTree α → α → BinTree α → BinTree α

open BinTree

instance [ToString α] : ToString (BinTree α) where
  toString :=
    let format c str    := s!"{c}: ({str})"
    let par c c' str    := s!"{c}{str}{c'}"
    let rec BinTree.toString : BinTree α → String
      | leaf         => ""
      | branch l x r =>
        let l' := BinTree.toString l
        let r' := BinTree.toString r
        let x' := par "(" ")" $ toString x
        x' ++ par "[" "]" (format "L" l' ++ " " ++ format "R" r')
    BinTree.toString

#eval (leaf : BinTree Int)
#eval branch leaf 3 leaf
#eval branch (branch leaf 3 leaf) 8 (branch leaf 4 leaf)
def t3 := branch (branch leaf 3 leaf) 8 (branch leaf 4 leaf)


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

def get : State σ σ :=
  fun s => (s, s)

def set (s : σ) : State σ Unit :=
  fun _ => (s, ())

def ok (x : α) : State σ α :=
  fun s => (s, x)

def andThen (first : State σ α) (next : α → State σ β) : State σ β :=
  fun s =>
    let (s', x) := first s
    next x s'

infixl:55 " ~~> " => andThen

-- def number (t : BinTree α) : BinTree (Nat × α) :=
--   let rec helper (n : Nat) : BinTree α → (Nat × BinTree (Nat × α))
--     | BinTree.leaf => (n, BinTree.leaf)
--     | BinTree.branch left x right =>
--       let (k, numberedLeft)  := helper n left
--       let (i, numberedRight) := helper (k + 1) right
--       (i, BinTree.branch numberedLeft (k, x) numberedRight)
--   (helper 0 t).snd

-- #eval number t3

def number (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper : BinTree α → State Nat (BinTree (Nat × α))
    | BinTree.leaf                => ok BinTree.leaf
    | BinTree.branch left x right =>
      helper left ~~> fun numberedLeft =>
      get ~~> fun n =>
      set (n + 1) ~~> fun () =>
      helper right ~~> fun numberedRight =>
      ok (BinTree.branch numberedLeft (n, x) numberedRight)
  (helper t 0).snd


-- testing states
def succ_state : State Nat Nat
  | 0     => (0, 1)
  | k + 1 =>
    let (n, m) := succ_state k
    (n + 1, m + 1)

#eval succ_state 3
#eval succ_state 24
#check ok ∘ (· + 1)
#eval succ_state 24
#eval succ_state ~~> ok ∘ (· + 1)
                 $ 24
#eval succ_state ~~> ok ∘ (· + 1)
                 ~~> ok ∘ (· + 1)
                 ~~> ok ∘ (· + 1)
                 ~~> ok ∘ (· + 1)
                 $ 24

-- o ok destroca dnv e acaba dando pra acumular..

#eval ok 3 "erro?"
#eval ok "ro" 3

#eval get $ ok 3 "erro?"
#eval set (ok 4 "erro") (ok 3 "erro?")
#eval get 3
#eval set 3 4

instance : Monad (State σ) where
  pure := ok
  bind := andThen

instance : Monad (State σ) where
  pure x := fun s => (s, x)
  bind first next :=
    fun s =>
      let (s', x) := first s
      next x s'

def increment (howMuch : Int) : State Int Int :=
  get >>= fun i =>
  set (i + howMuch) >>= fun () =>
  pure i

  #eval mapM increment [1, 2, 3, 4, 5] 0
--> (15, [0, 1, 3, 6, 10])
