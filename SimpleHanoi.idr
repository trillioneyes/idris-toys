module SimpleHanoi

data Hanoi : (disks, pegs : Nat) -> Type where
  hanoi : (positions : Vect d (Fin p)) -> Hanoi d p

dec : (k : Nat) -> Fin (S k) -> Fin (S k)
dec k fZ = fin k where
  fin : (k' : Nat) -> Fin (S k')
  fin Z = fZ
  fin (S k') = fS (fin k')
dec (S k) (fS i) = weaken (dec k i)

disksAt : Hanoi d p -> Fin p -> (p ** Vect p (Fin d))
--disksAt = disksAt' fZ where
--  disksAt' : 