import Lean.Data.Json

open Lean Json

namespace Tasks

inductive Status where
| done
| undone
| canceled
deriving Repr

open Status in
instance : ToString Status where
  toString s :=
    match s with
    | done => "done"
    | undone => "undone"
    | canceled => "canceled"



structure Task where
  name   : String
  desc   : String
  status : Status
deriving Repr


structure TodoList where
  title : String
  tasks : Array Task
deriving Repr

-- def TodoList.toJson (tl : TodoList) : Json :=
--   Json.mkObj [
--     ("title", Json.str tl.title),
--     ("tasks", Json.arr (tl.tasks.map).toArray)
--   ]


end Tasks
