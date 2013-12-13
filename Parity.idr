module Parity

data Parity : Nat -> Type where
  even : Parity (k+k)
  odd : Parity (S (k+k))

invert : Parity k -> Parity (S k)
invert even = ?inv_even
invert odd = ?inv_odd

combine : Parity k -> Parity j -> Parity (k + j)
combine even = ?comb_even
combine odd = ?comb_odd

down : Parity (S (S k)) -> Parity k
down = ?down

parity : (n : Nat) -> Parity n
parity Z = ?par_Z
parity (S k) = ?par_k

{-data HasParity : Nat -> Parity -> Type where
  even_def : (k : Nat) -> HasParity (k+k) Even
  odd_def : (k : Nat) -> HasParity (S (k+k)) Odd-}

---------- Proofs ----------

Parity.inv_even = proof
  compute
  intro
  exact odd


