def g (trans : Array α → Array α) (l : Array α) : Array (Array α) :=
sorry

inductive JSON where
| true   : JSON
| false  : JSON
| null   : JSON
| string : String → JSON
| number : Float  → JSON
| object : List (String × JSON) → JSON
| array  : List JSON → JSON
deriving Repr

structure Serializer where
Contents  : Type
serialize : Contents → JSON

def Str : Serializer :=
{ Contents  := String,
  serialize := JSON.string
}

#check fun x y => x + y
