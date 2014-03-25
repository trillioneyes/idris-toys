module Permutation

-- a type for representing permutations of n elements
data Permutation : Nat -> Type where
  Nil : Permutation Z
  (::) : Fin (S n) -> Permutation n -> Permutation (S n)


mutual
  permute : Permutation n -> Vect n elt -> Vect n elt
  permute p v = reverse $ permute' p v

  permute' : Permutation n -> Vect n elt  -> Vect n elt
  permute' [] [] = []
  permute' {elt} (k::p) (a::as) = insert (permute' p as) k
    where insert : Vect n elt -> Fin (S n) -> Vect (S n) elt
          insert xs fZ = a :: xs
          insert (x::xs) (fS k) = x :: insert xs k


--permutation : Permutation n -> Vect n (Fin n)
--permutation p = permute p

id : Permutation n
id {n=Z} = []
id {n=S n} = last :: id