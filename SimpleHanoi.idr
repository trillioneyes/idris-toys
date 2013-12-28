module SimpleHanoi
import Data.Vect

-- We'll represent Hanoi states as vectors. The nth element of a vector
-- describes the position of the nth disk (we'll use the convention that the
-- 0th disk is the smallest), so a state with 4 disks and 3 pegs where the
-- smallest disk is on the middle peg, the middle 2 disks are on the left peg,
-- and the largest disk is on the right peg would be:
-- [1, 0, 0, 2]
Hanoi : (disks, pegs : Nat) -> Type
Hanoi d p = Vect d (Fin p)

-- "decrement", not "Decision"
dec : (k : Nat) -> Fin (S k) -> Fin (S k)
dec k fZ = fin k where
  fin : (k' : Nat) -> Fin (S k')
  fin Z = fZ
  fin (S k') = fS (fin k')
dec (S k) (fS i) = weaken (dec k i)

-- "The peg p is empty in hanoi configuration h"
Empty : Hanoi d p -> Fin p -> Type
Empty hanoi peg = Not (Elem peg hanoi)

-- This should return a more helpfully-typed result in the Right case
topDisk : (h:Hanoi d p) -> (peg : Fin p) -> Either (Empty h peg) (Fin d)


{-
disksAt : Hanoi d p -> Fin p -> (n ** Vect n (Fin d))
disksAt = disksAt' {n=Z} fZ [] where
  disksAt' : Fin (S n) -> Vect n a -> Hanoi d p -> Fin p -> 
-}