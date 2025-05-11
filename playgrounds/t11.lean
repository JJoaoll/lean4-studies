
inductive CBTree where
  | leaf : CBTree
  | sup : (Nat → CBTree) → CBTree

open CBTree

#check leaf
#check sup $ fun _ => (sup (fun _ => leaf))

namespace CBTree

def succ (t : CBTree) : CBTree :=
  sup (fun _ => t)

def toCBTree : Nat → CBTree
  | 0 => leaf
  | n+1 => succ (toCBTree n)

def omega : CBTree :=
  sup toCBTree

end CBTree



---------------------------------------------------------------------------------------

def teste : { w : List α × List β // w.1.length = w.2.length} := sorry


#print Subtype

structure RGB where
  red   : {n : Nat // n < 256}
  green : {n : Nat // n < 256}
  blue  : {n : Nat // n < 256}
deriving Repr

def Hour   := {n : Nat // 1 < n ∧ n ≤ 24}
def Minute := {n : Nat // 1 < n ∧ n ≤ 60}
def Second := {n : Nat // 1 < n ∧ n ≤ 60}

structure Time where
  sec  : Second
  min  : Minute
  hour : Hour


notation:10 "triv " n => ⟨n, by simp⟩
notation:10 n "_" => ⟨n, by simp⟩

def yellow : RGB := {red   := 255 _
                    ,green := 255 _
                    ,blue  := 0   _}
#eval yellow

-- def estranho : RGB := {red   := 250 _
--                       ,green := 25120934821315 _
--                       ,blue  := 01292193 _}
-- #eval estranho



def prod (α : Type) (n : Nat) :=
  match n with
  | 0     => Unit
  | 1     => α
  | n + 1 => α × prod α n

def fromList (l : List Type) : Type :=
  match l with
  | []      => Unit
  | [t]     => t
  | t :: ts => t × fromList ts

#check prod Int
#check Nat → String
