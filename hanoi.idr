data Permutation : (n : Nat) -> Type where
  nth : Fin (fact k) -> Permutation k

permutation : Permutation k -> Vect k a -> Vect k a

  

{-
data Hanoi : (pegs : Nat) -> (disks : Nat) ->
             Vect pegs (List (Fin disks)) -> Type
-}