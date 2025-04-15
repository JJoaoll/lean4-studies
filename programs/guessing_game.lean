open Ordering in
def judge (answer : Nat) (shot : Option Nat) : IO Bool := do {
  let stdout ← IO.getStdout

  match shot with
  | none =>
    stdout.putStrLn "Escolha um número, por favor."
    return false

  | some val =>
    match compare val answer with
    | lt => stdout.putStrLn "Chutou baixo!" ; return false
    | eq => stdout.putStrLn "Você acertou!!"; return true
    | gt => stdout.putStrLn "Chutou alto!"  ; return false
}


partial def game (answer : Nat) : IO Unit := do {
  let stdin ← IO.getStdin

  let guess ← stdin.getLine
  let verdict ← judge answer guess.trim.toNat?

  if !verdict then
    game answer
}


def main : IO Unit := do
  let stdout ← IO.getStdout

  let secret_number ← IO.rand 1 100

  stdout.putStrLn "Bem vindo ao jogo da adivinhação!"
  stdout.putStrLn "Escolha um número (1-100) e vamos jogar!"

  game secret_number

  stdout.putStrLn "Fim de jogo!"
