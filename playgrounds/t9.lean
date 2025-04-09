-- Monads

-- pure : α → m α
-- bind : m α × (α → m β) → m β

-- nullable
-- Optional
-- Exceptions
-- Result<_, _>

-- Monads

-- pure : α → m α
-- bind : m α × (α → m β) → m β

#print Option

def opt_five : Option Nat :=
  pure 5

def opt_four : Option Nat :=
  none

#eval opt_five
#eval opt_four

-- pure : α → m α
-- bind : m α × (α → m β) → m β

def try_div (n m : Nat) : Option Nat :=
  if m = 0 then
    none
  else
    some (n / m)

#check try_div
#check try_div 3

#eval try_div 3 4
#eval try_div 4 3

def std (n : Nat) : Option Nat :=
  let opt_x := try_div n 2
  match opt_x with
  | none => none
  | some val =>
    let opt_y := try_div val 3
    match opt_y with
    | none => none
    | some val' =>
      let opt_z := try_div val' 5
      match opt_z with
      | none => none
      | some val'' => some val''

#eval std 555

def std2 (n : Nat) : Option Nat :=
  bind (bind (try_div n 2) (try_div · 3)) (try_div · 5)

#eval std2 555

def std3 (n : Nat) : Option Nat :=
  try_div n 2 >>= (try_div · 3)
              >>= (try_div · 5)

#eval std3 555

def new (n : Nat) : Option Nat := do
  let x ← try_div n 2
  let y ← try_div x 0
  let z ← try_div y 5
  return z

#eval new 555

def hello_monad : IO Nat := do {
  let x ← pure $ 3 + 5
  let y ← pure $ 6 + 6
  return x + y
}

-- Monads

-- pure : α → m α
-- bind : m α × (α → m β) → m β
--
