-- Descrição:
-- Dado um número inteiro positivo, implemente uma função que calcula a soma recursiva dos
-- dígitos até que o resultado tenha apenas um dígito. Este problema é conhecido como
-- "Soma dos Dígitos Recursiva" ou "Número Digital".

-- Exemplo:
-- Para o número 9875, a função deve retornar 2, pois:
-- 9 + 8 + 7 + 5 = 29
-- 2 + 9 = 11
-- 1 + 1 = 2
--
-- 9875 % 9 = [(9 · 10³) + (8 · 10²) + (7 · 10¹) + (5 · 10⁰)] % 9
--          = [(9 · 1) + (8 · 1) + (7 · 1) + (5 · 1)] % 9
--          = [9  + 8 + 7 + 5 ] % 9
--          = 29 % 9
--          = [(2 · 10¹) + (9 · 10⁰)] % 9
--          = [(2 · 1) + (9 · 1)] % 9
--          = [2 + 9 ] % 9
--          = 11 % 9
--          = [(1 · 10¹) + (1 · 10⁰)] % 9
--          = [(1 · 1) + (1 · 1)] % 9
--          = [1 + 1 ] % 9
--          =  2 % 9

-- 9875 % 9 = [(9 · 10³) + (8 · 10²) + (7 · 10¹) + (5 · 10⁰)] % 9
--          = [(9 · 1) + (8 · 1) + (7 · 1) + (5 · 1)] % 9
--          = [9  + 8 + 7 + 5 ] % 9
--          = 29 % 9
--          = [(2 · 10¹) + (9 · 10⁰)] % 9
--          = [(2 · 1) + (9 · 1)] % 9
--          = [2 + 9 ] % 9
--          = 11 % 9
--          = [(1 · 10¹) + (1 · 10⁰)] % 9
--          = [(1 · 1) + (1 · 1)] % 9
--          = [1 + 1 ] % 9
--          =  2 % 9

def solucao := fun x => x % 9

#eval 9875 % 9
#eval 7567 % 9

#check (· ∣ ·)
#eval 3 ∣ 4
#eval 2 ∣ 4
#check (· ∣ 4)
section existencial

variable {α : Type}
def p.{u} {α : Type u} := α → Prop

#check @p $ @p $ @p $ p


theorem t2 : 2 ∣ 4 := by
  exists 2
#print Exists
#check @Exists.intro Nat (· ∣ 4) 2 (t2)


-- #check Exists.intro
-- #check Exists (fun x : α => p x)

end existencial
