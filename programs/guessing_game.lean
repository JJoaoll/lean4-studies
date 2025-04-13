open IO

partial def game (answer : Nat) : IO Unit := do
  let stdin  ← IO.getStdin
  let stdout ← IO.getStdout

  let guess ← stdin.getLine
  match guess.trim.toNat? with
  | none =>
      stdout.putStrLn "Escolha um número, por favor."
      game answer
  | some n =>
    if n < answer then
      stdout.putStrLn "Chutou baixo!"
      game answer
    else if n > answer then
      stdout.putStrLn "Chutou alto!"
      game answer
    else
      stdout.putStrLn "Você acertou!!"



def main : IO Unit := do
  let stdout ← IO.getStdout

  let secret_number ← rand 1 100

  stdout.putStrLn "Bem vindo ao jogo da adivinhação!"
  stdout.putStrLn "Escolha um número (1-100) e vamos jogar!"

  game secret_number

  stdout.putStrLn "Fim de jogo!"
