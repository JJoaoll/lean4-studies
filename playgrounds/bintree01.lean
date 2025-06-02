
section
universe u

-- Non void trees
structure Tree (α : Type u) where
  sons : List (Tree α)
  val : α 
deriving Repr, Inhabited
end

open Tree

#eval Tree.mk [] 3

def leaf (x : α) := Tree.mk [] x
#eval leaf 3
def t1 := Tree.mk [leaf 4, leaf 5, Tree.mk [leaf 3] 7] 8

-- dependnt tp issue
inductive Dir where
  | UP
  | Down (n : Nat)
  | X
deriving Repr, Inhabited

structure Path where
  dirs : List Dir
deriving Repr, Inhabited


#check List.reduceOption 
#eval [some 3, none].reduceOption
#check (t1.sons).map (λ _ => [Path.mk [Dir.UP]])

-- aceitando repetições
partial def Tree.pathTo [DecidableEq α] (t : Tree α) (goal : α) : List Path :=
  if t.val = goal then
    [{dirs := [Dir.X]}]
  else
    let ts := (·.pathTo) <$> t.sons
    ts.map (·.pathTo goal) |>  ((·.map) ∘ (·.map)) (Dir.X :: ·) |> List.flatten


-- def Tree.path_from_to (t : Tree α) (x y : α) : Option Path := do {
