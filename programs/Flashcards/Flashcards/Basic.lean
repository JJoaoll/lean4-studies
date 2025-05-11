import Lean.Data.Json
import Cli

open Lean Json

namespace Flashcard

structure Flashcard where
  question : String -- primary key
  answer   : String
deriving Repr

end Flashcard
open Flashcard

namespace Parser

instance : FromJson Flashcard where
  fromJson? j := do {
    let question ← j.getObjValAs? String "question"
    let answer   ← j.getObjValAs? String "answer"

    -- and nothing else (improve how?)
    let obj ← j.getObj?

    if obj.size ≠ 2 then
      throw s!"Json has more than it should have. Something is wrong.
              \n {j.pretty}"
    else
      return Flashcard.mk question answer
  }

instance : ToJson Flashcard where
  toJson f :=
    Json.mkObj [
      ("question", Json.str f.question),
      ("answer"  , Json.str f.answer  ),
    ]

def test : Json :=
  json% {
    "cataratas": 42,
    "question" : "seu nome",
    "answer"   : "cjr"
  }

#eval (fromJson? test : Except String Flashcard)

end Parser

namespace FileIO

open System Parser

def readJson (path : FilePath) : IO (Except String Json) := do
  let content ← IO.FS.readFile path
  match Json.parse content with
  | .ok j => return .ok j
  | .error e => return .error $ s!"Something's wrong with: {path.toString}\n" ++ e

def writeJson (path : FilePath) (data : α) [ToJson α] : IO Unit := do
  let jsonStr := Json.pretty (toJson data)
  IO.FS.writeFile path jsonStr

def

end FileIO
