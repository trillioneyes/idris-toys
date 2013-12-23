module SimpleHanoi

data Hanoi : (disks, pegs : Nat) -> Type where
  hanoi : (positions : Vect d (Fin p)) -> Hanoi d p

-- "decrement", not "Decision"
dec : (k : Nat) -> Fin (S k) -> Fin (S k)
dec k fZ = fin k where
  fin : (k' : Nat) -> Fin (S k')
  fin Z = fZ
  fin (S k') = fS (fin k')
dec (S k) (fS i) = weaken (dec k i)

-- "The peg p is empty in hanoi configuration h"
Empty : Hanoi d p -> Fin p -> Type
Empty (hanoi h) peg = Not (Elem peg h)

topDisk : (h:Hanoi d p) -> (peg : Fin p) -> Either (Empty h peg) (Fin d)


{-
disksAt : Hanoi d p -> Fin p -> (n ** Vect n (Fin d))
disksAt = disksAt' {n=Z} fZ [] where
  disksAt' : Fin (S n) -> Vect n a -> Hanoi d p -> Fin p -> 
-}