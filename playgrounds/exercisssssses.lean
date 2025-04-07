-- Given an array arr[] and an integer k, the task is to reverse every
-- subarray formed by consecutive K elements.

-- Examples:

--     Input: arr[] = [1, 2, 3, 4, 5, 6, 7, 8, 9], k = 3
--     Output: 3, 2, 1, 6, 5, 4, 9, 8, 7

--     Input: arr[] = [1, 2, 3, 4, 5, 6, 7, 8], k = 5
--     Output: 5, 4, 3, 2, 1, 8, 7, 6

--     Input: arr[] = [1, 2, 3, 4, 5, 6], k = 1
--     Output: 1, 2, 3, 4, 5, 6

--     Input: arr[] = [1, 2, 3, 4, 5, 6, 7, 8], k = 10
--     Output: 8, 7, 6, 5, 4, 3, 2, 1

open List

-- missing correcting
partial def List.crop (l : List α) (n : Nat) : List (List α) :=
  if l.length ≥ n then
   l.take n :: crop (l.drop n) n
  else
    [l.take n]

#eval [1,2,3,4,5].crop 3
#eval List.crop [1,2,3,4,5,6,7,8,9,10] 4

partial def challenge (l : List α) (n : Nat) : List α :=
  l |> (crop · n) |> (map reverse) |> flatten

partial def challengeR (n : Nat) : List α → List α :=
  flatten ∘ map reverse ∘ (crop · n)

#eval challenge [1, 2, 3, 4, 5, 6] 2
#eval challenge [1, 2, 3, 4, 5, 6] 3
#eval challenge [1, 2, 3, 4, 5, 6] 4
#eval challenge [1, 2, 3, 4, 5, 6] 1

#check filter

def oneToFive := [1, 2, 3, 4, 5]

partial def quicksort : List Float → List Float
  | []      => []
  | x :: xs =>
    let smallerThanX := quicksort $ filter (· ≤ x) xs
    let biggerThanX  := quicksort $ filter (· > x) xs
    smallerThanX ++ [x] ++ biggerThanX

#eval quicksort [1,4,5,2,5,1,6,7,2,34341,5,34,2,41,23,4123,123,1243,5123,523,5]

-- Desafio:
-- Complexidade: Iniciante
-- Tipo: Estrutura de dados O(n)

-- Tags para pesquisa Crtl + f ignorem:
--  desafio, iniciante, estrutura de dados, O(n), complexidade, linear, loop, algoritmo, desafios iniciantes, estruturas lineares, programação

-- Desafio: Retorne o maior e menor número de um Array.

-- Linguagem: A que você se sinta mais a vontade em usar

-- Array: nums = [3, 8, 2, 6, 7];

-- Prazo: 2 Dias (23.03.2025)
open Ordering in
def put_if_fits [Ord α] (a : α) (pair : α × α) : α × α :=
  let lowest  := pair.1
  let highest := pair.2
  match compare a lowest with
  | lt => ⟨a, highest⟩
  | _  =>
    match compare a highest with
    | gt => ⟨lowest, a⟩
    | _  => pair

open Functor in
def menor_e_maior [Ord α] : List α → Option (α × α)
  | []      => none
  | [x]     => some ⟨x, x⟩
  | x :: xs => map (put_if_fits x) (menor_e_maior xs)

#eval menor_e_maior [3, 8, 2, 6, 7] --> some (2, 8)
#eval menor_e_maior [3, 4, 4, 5]    --> some (3, 5)

def zip_matrix_with (op : α → β → γ) : List α → List β → List (List γ)
  | []     , _  => []
  | a :: as, bs => map (op a) bs :: zip_matrix_with op as bs

#eval zip_matrix_with (· * ·) [1, 2, 3] [4, 5, 6]

inductive MyNat where
| zero : MyNat
| succ : MyNat → MyNat

open MyNat

@[match_pattern]
abbrev O := MyNat.zero

@[match_pattern]
abbrev S := MyNat.succ

#eval O
#eval S O

instance : ToString MyNat where
  toString :=
    let rec nts : MyNat → String
      | O   => "O"
      | S k  => "S " ++ nts k
    nts

#eval O
#eval S O
#eval S (S O)
def three := S (S (S O))
def four  := S (S (S (S O)))
#eval S (S (S (S (S O))))
#eval S (S (S (S (S (S O)))))
#eval S (S (S (S (S (S (S O))))))

def MyNat.add : MyNat → MyNat → MyNat
  | O  , m => m
  | S k, m => S (k.add m)

  #eval three.add four



inductive User where
| client (id : Int) (nome : String) (divida : Float) : User
-- | adm    (id : Int) (nome : String)                  : User
deriving Repr

open User

#eval (client 42 "pedro" 33)

def getName (u : User) : String :=
  match u with
  | client _ nome _ => nome
  -- | adm _ nome      => nome

def getSalary (u : User) : Float :=
  match u with
  | client _ _ salary => salary

def pedro := (client 42 "pedro" 33)
def lara  := (client 24 "lara" 300)

def juntaUsers (u₁ u₂ : User) : User :=
  match u₁, u₂ with
  | client id₁ nome₁ salary₁,
    client id₂ nome₂ salary₂ =>
      client (id₁ + id₂) (nome₁ ++ " " ++ nome₂) (salary₁ + salary₂)

#eval getName pedro
#eval getSalary pedro
#eval juntaUsers pedro lara
#eval getSalary (juntaUsers pedro lara)
#eval (getSalary pedro) + (getSalary lara)

theorem t1 : ∀(u u' : User),
  getSalary (juntaUsers u u') = (getSalary u) + (getSalary u')
  :=
  by {
    intros u u'
    cases u
    cases u'
    rw [getSalary]
    rw [getSalary]
    rw [getSalary]
    rw [juntaUsers]
  }

def complement C :=
  match C with
  | 'A' => 'T'
  | 'T' => 'A'
  | 'C' => 'G'
  | 'G' => 'C'
  | _   => C

open List in
def solution :=  String.mk ∘ reverse ∘ map complement ∘ String.toList

-- #eval solution "AAAACCCGGT"

