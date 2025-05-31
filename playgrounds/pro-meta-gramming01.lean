import Lean

open Lean Lean.Expr Lean.Meta

#check Eq.trans

theorem tst {α} (a : α) (f : α → α) (h : ∀ a, f a = a) : f (f a) = a := by
  apply Eq.trans
  apply h
  apply h

#print tst
#reduce tst
#check tst
