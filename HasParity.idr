module HasParity

data Parity = Even | Odd

data HasParity : Nat -> Parity -> Type where
  def_even : {k : Nat} -> HasParity (k+k) Even
  def_odd : {k : Nat} -> HasParity (S (k+k)) Odd