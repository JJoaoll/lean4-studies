-- examples with equality
#check Eq
#check @Eq
#check Eq.symm
#check @Eq.symm


#print Eq.symm


-- examples with And
#check And
#check And.intro
#check @And.intro

-- a user-defined function
def foo {α : Type u} (x : α) : α := x

#check foo
#check @foo
#print foo

set_option pp.explicit false
set_option pp.universes false
set_option pp.notation true

#check 2 + 2 = 4
#check 2 + _
#check (2 + ·) 8

#reduce (fun x => x + 2) = (fun x => x + 3)
#check (fun x => x + 1) 1
