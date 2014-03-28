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


finish : Fin n -> Permutation n
finish fZ = id
finish (fS k) = fS (zeroize k) :: finish k
  where zeroize : Fin m -> Fin m
        zeroize fZ = fZ
        zeroize (fS k) = fZ

swap : Fin n -> Fin n -> Permutation n
swap (fS j) (fS k) = fZ :: swap j k
swap (fS j) fZ = fS j :: finish j
swap fZ (fS k) = fS k :: finish k
swap fZ fZ = id
