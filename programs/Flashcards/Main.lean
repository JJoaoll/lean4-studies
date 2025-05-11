import Cli
import Flashcards

open Cli Flashcard
def default_path := "./flashcards.json"

namespace Run

#check Parsed.variableArgsAs?

def new (p : Parsed) : IO UInt32 := do {
  match p.variableArgsAs? String with
  | none => return 1
  | some #[question, answer] =>
    let flashcard : Flashcard := ⟨question, answer⟩


    return 3

  | _ => return 2






}


end Run

namespace Cmd


end Cmd

def main : IO Unit :=
  IO.println s!"Hello, world!"
