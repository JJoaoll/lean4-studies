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
