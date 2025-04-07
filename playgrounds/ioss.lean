
-- monad
-- return/pure : α → m α
-- bind : m α × (α → m β) → m β

#check Option
#print Option

def opt_five := some 5
def opt_six : Option Nat := none

#check opt_five
#check opt_six

-- monad
-- return/pure : α → m α
-- bind : m α × (α → m β) → m β

def tryDiv2 (n : Nat) : Option Nat :=
  if n % 2 = 0 then
    some (n / 2)
  else
    none

def rust (n : Nat) : IO Nat := do
  let opt_x ← pure $ tryDiv2 n
  match opt_x with
  | none     => return 0
  | some val =>
    let opt_y ← pure $ tryDiv2 val
    match opt_y with
    | none     => return 0
    | some val =>
      let opt_z ← pure $ tryDiv2 val
      match opt_z with
      | none     => return 0
      | some val =>
        return val

#eval rust 88

-- monad
-- return/pure : α → m α
-- bind : m α × (α → m β) → m β

-- #eval bind (tryDiv2 88) tryDiv2
-- #eval bind (bind (tryDiv2 88) tryDiv2) tryDiv2
-- #eval tryDiv2 88 >>= tryDiv2
--                  >>= tryDiv2

-- #eval tryDiv2 5 >>= tryDiv2
--                 >>= tryDiv2

-- #eval tryDiv2 88 >>= tryDiv2
--                  >>= pure ∘ (· + 2)
--                  >>= tryDiv2


-- def rust (n : Nat) : IO Nat := do
--   let opt_x ← pure $ tryDiv2 n
--   match opt_x with
--   | none     => return 0
--   | some val =>
--     let opt_y ← pure $ tryDiv2 val
--     match opt_y with
--     | none     => return 0
--     | some val =>
--       let opt_z ← pure $ tryDiv2 val
--       match opt_z with
--       | none     => return 0
--       | some val =>
--         return val

def nonRust (n : Nat) : Option Nat := do
  let x ← tryDiv2 n
  let y ← tryDiv2 x
  let z ← tryDiv2 (y + 2)
  return z

#eval nonRust 88
#eval rust 88

#eval tryDiv2 8
#eval tryDiv2 5

#check "oi"
#check String
#check Type
