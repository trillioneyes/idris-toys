module Permutation

%default total

-- a type for representing permutations of n elements
data Permutation : Nat -> Type where
  Nil : Permutation Z
  (::) : Fin (S n) -> Permutation n -> Permutation (S n)

%name Permutation p, q, r
%name Fin i, k, j


mutual
  permute : Permutation n -> Vect n elt -> Vect n elt
  permute = permute'

  permute' : Permutation n -> Vect n elt  -> Vect n elt
  permute' [] [] = []
  permute' {elt} (k::p) (a::as) = insert (permute' p as) k
    where insert : Vect n elt -> Fin (S n) -> Vect (S n) elt
          insert xs fZ = a :: xs
          insert [] (fS i) = [a]
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


-- Since each element of a permutation is a different type, we can't put
-- them in lists/vectors. Permutations themselves must be complete, and
-- heterogeneous lists discard too many invariants. So we need a new type
-- for permutation element accumulators.
data Fragment : (lowerBound:Nat) -> (length:Nat) -> Type where
  FNil : Fragment n Z
  FCons : Fin n -> Fragment (S n) l -> Fragment n (S l)

fuse : Fragment (S n) l -> Permutation n -> Permutation (l + n)
fuse FNil p = p
fuse (FCons i x) p ?= fuse x (i :: p)

noFinZ : Fin n -> (k ** n = S k)
noFinZ {n = S k} _ = (k ** refl)
noFinZ {n = Z} fZ impossible
noFinZ {n = Z} (fS _) impossible

contract' : Fin (S n) -> Permutation (S n) -> Fragment (S (S n)) l -> Permutation (l + n)
contract' {n} {l} fZ (i :: p) f = fuse f' p where
  f' : Fragment (S n) l
  f' = ?decrementFragment
contract' (fS i) (k :: p) f with (noFinZ i)
  contract' {n=S x} (fS i) (k :: p) f | ((x ** refl)) ?= contract' i p (FCons k f)

-- helper function for `compose`: given an index and a permutation, remove
-- the index and return a smaller permutation
contract : Fin (S n) -> Permutation (S n) -> Permutation n
contract k p = (contract' k p FNil)


-- compose : Permutation n -> Permutation n -> Permutation n
-- compose Nil Nil = Nil

---------- Proofs ----------

Permutation.fuse_lemma_1 = proof
  intros
  rewrite sym (plusSuccRightSucc l n)
  exact value


Permutation.contract'_lemma_1 = proof
  intros
  rewrite plusCommutative (S x) l
  let newval = replace (plusCommutative (S l) x) value
  rewrite sym (plusSuccRightSucc x l)
  trivial


