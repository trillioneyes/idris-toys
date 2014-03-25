module Permutation

-- a type for representing permutations of n elements
data Permutation : Nat -> Type where
  Nil : Permutation Z
  (::) : Fin (S n) -> Permutation n -> Permutation (S n)


mutual
  permute : Permutation n -> Vect n elt -> Vect n elt
  permute = permute'

  permute' : Permutation n -> Vect n elt  -> Vect n elt
  permute' [] [] = []
  permute' {elt} (k::p) (a::as) = insert (permute' p as) k
    where insert : Vect n elt -> Fin (S n) -> Vect (S n) elt
          insert xs fZ = a :: xs
          insert (x::xs) (fS k) = x :: insert xs k


permutation : Permutation n -> Vect n (Fin n)
permutation {n} p = permute p (fins n)
  where fins : (n:Nat) -> Vect n (Fin n)
  	fins Z = []
	fins (S k) = fZ :: map fS (fins k)
permutation' : Permutation n -> Vect n Nat
permutation' p = map cast (permutation p)

id : Permutation n
id {n=Z} = []
id {n=S n} = fZ :: id

reverse : Permutation n
reverse {n=Z} = []
reverse {n=S n} = last :: reverse

swap : Fin n -> Fin n -> Permutation n
-- hints for writing swap:
-- *Permutation> permutation' [4,1,1,1,0]
-- [4, 1, 2, 3, 0] : Vect 5 Nat
-- *Permutation> permutation' [0,2,1,0,0]
-- [0, 3, 2, 1, 4] : Vect 5 Nat
-- *Permutation> permutation' [7,1,1,1,1,1,1,0]
-- [7, 1, 2, 3, 4, 5, 6, 0] : Vect 8 Nat
-- *Permutation> permutation' [0,0,3,1,1,0,0,0]
-- [0, 1, 5, 3, 4, 2, 6, 7] : Vect 8 Nat
