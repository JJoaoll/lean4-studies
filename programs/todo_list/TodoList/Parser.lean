import Lean.Data.Json
import TodoList.Tasks

open Lean Json
open Tasks Status

namespace Parser

------------------------------------------------------------------------------------------
/-                                FromJsons:                                            -/
------------------------------------------------------------------------------------------

instance : FromJson Status where
  fromJson?
    | Json.str "done"     => .ok done
    | Json.str "undone"   => .ok undone
    | Json.str "canceled" => .ok canceled
    | Json.str other      => .error s!"Invalid format: {other}"
    | _                   => .error "The received format was not even a string!"

instance : FromJson Task where
  fromJson? j := do {
    let name ← j.getObjValAs? String "name"
    let desc ← j.getObjValAs? String "desc"

    let status ← j.getObjValAs? Status "status"

    return Task.mk name desc status
  }


instance : FromJson TodoList where
  fromJson? j := do {
    let title     ← j.getObjValAs? String "title"
    let tasksJson ← j.getObjValAs? (Array Json) "tasks"

    -- efficiency
    let mut tasks : List Task := [];
    for t in tasksJson do {
      let t ← fromJson? t
      tasks := tasks.concat t
    }

    return TodoList.mk title tasks.toArray
  }

------------------------------------------------------------------------------------------
/-                                  ToJsons:                                            -/
------------------------------------------------------------------------------------------

instance : ToJson Status where
  toJson
    | done     => json% "done"
    | undone   => json% "undone"
    | canceled => json% "canceled"

instance : ToJson Task where
  toJson t :=
    Json.mkObj [
      ("name"  , Json.str t.name),
      ("desc"  , Json.str t.desc),
      ("status", toJson t.status)
    ]

instance : ToJson TodoList where
  toJson tdl :=
    Json.mkObj [
      ("title", Json.str tdl.title),
      ("tasks", Json.arr $ tdl.tasks.map toJson)
    ]

------------------------------------------------------------------------------------------
/-                                    Tests:                                            -/
------------------------------------------------------------------------------------------

def myTodoList : Json :=
  json% {
    "title": "My Todo List",
    "tasks": [
      { "name": "Buy milk", "desc": "2 liters", "status": "done" },
      { "name": "Call mom", "desc": "Sunday", "status": "undone" }
    ]
  }

def myStatus : Json :=
  json% "undone"

def myTask : Json :=
  json% {
    "name": "Write documentation",
    "desc": "Finish writing Lean4 docs",
    "status": "done"
  }

#eval IO.println myTodoList.pretty
#eval IO.println myStatus.pretty
#eval IO.println myTask.pretty

#eval (fromJson? myStatus   : Except String Status)
#eval (fromJson? myTask     : Except String Task)
#eval (fromJson? myTodoList : Except String TodoList)

#eval (myStatus   |> toJson |> fromJson? : Except String Status  )
#eval (myTask     |> toJson |> fromJson? : Except String Task    )
#eval (myTodoList |> toJson |> fromJson? : Except String TodoList)

-- Se tiver errado, continua errado :P
#eval (match (fromJson? myStatus : Except String Status) with
       | .error _   => myStatus
       | .ok status => toJson status)

#eval (match (fromJson? myTask : Except String Task) with
       | .error _   => myTask
       | .ok task => toJson task)

#eval (match (fromJson? myTodoList : Except String TodoList) with
       | .error _   => myTodoList
       | .ok todo_list => toJson todo_list)

------------------------------------------------------------------------------------------
/-                                    Correctness?:                                     -/
------------------------------------------------------------------------------------------

#check Except.ok.inj

theorem parser_status_correctness :
  (∀ (status : Status), (fromJson? ∘ toJson) status = .ok status) ∧
  ∀ (status? : Json),
  (match (fromJson? status? : Except String Status) with
   | .ok status => toJson status
   | .error _   => status?) = status?
   := by {

   constructor
   · intro status
     cases status <;> simp [toJson, fromJson?]

   · intro json
     split <;> simp [toJson, fromJson?] at *
     · split at *
       · split <;>
         any_goals simp
         all_goals repeat (apply Except.ok.inj ; assumption)
         all_goals (repeat rename_i _ _ h ; have := Except.ok.inj h ; contradiction)

       · split
         any_goals simp
         all_goals repeat (apply Except.ok.inj ; assumption)
         all_goals (repeat rename_i _ _ h ; have := Except.ok.inj h ; contradiction)

       · split
         any_goals simp
         all_goals repeat (apply Except.ok.inj ; assumption)
         all_goals (repeat rename_i _ _ h ; have := Except.ok.inj h ; contradiction)

       · split
         simp
         all_goals contradiction

       · split
         any_goals contradiction

}

theorem parser_task_correctness :
  (∀ (task : Task), (fromJson? ∘ toJson) task = .ok task) ∧
  ∀ (task? : Json),
  (match (fromJson? task? : Except String Task) with
   | .ok task => toJson task
   | .error _   => task?) = task?
   := by {

   constructor
   · intro task
     simp [toJson, fromJson?, mkObj, getObjValAs?, str, parser_task_correctness]
     split

     all_goals admit

   · admit
}

theorem parser_todolist_correctness :
  ∀ (todolist : TodoList), (fromJson? ∘ toJson) todolist = .ok todolist ∧
  ∀ (todolist? : Json),
  (match (fromJson? todolist? : Except String TodoList) with
   | .ok todolist => toJson todolist
   | .error _   => todolist?) = todolist?
   := by {

  admit
}

end Parser
