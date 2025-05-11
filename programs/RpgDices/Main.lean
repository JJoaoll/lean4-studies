import RpgDices
import Cli

open Cli

namespace Run

#check Parsed.positionalArgs
#check Parsed.positionalArgs
#check Parsed.variableArgsAs?
#check Parsed.variableArgsAs!
#check Parsed.positionalArg!
#check Parsed.Arg.as?
#check String.toNat!

def randNums (n : Nat) (min max : Nat) : IO (Array Nat) := do
  let mut result := #[]
  for _ in [:n] do
    let r ← IO.rand min.succ max.succ
    result := result.push r
  return result

def str_to_rolls? (s : String) : Option (Nat × Nat) := do {
  match s.splitOn "d" with
  | ["", d_size]    => some (1, ← d_size.toNat?)
  | [rolls, d_size] => some (← rolls.toNat?, ← d_size.toNat?)
  | _ => none
}

def roll (p : Parsed) : IO UInt32 := do {
  match p.variableArgsAs? String with
  | none => IO.println "Invalid Argument format. Use -h to see how to use it." ; return 1
  | some dices =>

    let mut rolls? : Option (Nat × Nat) := none;

    for d in dices do {
      rolls? := str_to_rolls? d
      match rolls? with
      | none => IO.println s!"Invalid arg format: {d}"
      | some r => IO.println $ "d" ++ toString r.2 ++ ": " ++ toString (← randNums r.1 0 r.2)
    }

    return 0
}


end Run

namespace Cmd

  def roll : Cmd := `[Cli|
    exampleCmd VIA Run.roll ; ["0.0.1"]
    "This command rolls a dice with some especification."

    FLAGS:
      h;   "asks for help" --help

    ARGS:
      ...dices : Array String; "Receive a list like 2d6 d8 3d20"

  ]

end Cmd

def main (args : List String) : IO UInt32 := do {
  IO.println "Here are your results:";
  Cmd.roll.validate args;
}

#eval "4d5".splitOn "d"
-- #eval str_to_rolls? "4d5"
#eval "d12".splitOn "d"
-- #eval str_to_rolls? "d12"

#check Parsed.variableArgsAs?
#check Parsed.flags
