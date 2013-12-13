module Induction
import Data.Vect


All : (a : Type) -> (P : a -> Type) -> Type
All a P = (k:a) -> P k

induction : (P : Nat -> Type)                    ->
            (base : P 0)                         ->
            (step : (n : Nat) -> P n -> P (S n)) ->
            All Nat P
induction P base step Z = base
induction P base step (S n) = step n (induction P base step n)


takeFSHasFirst : {k:Fin (S n), xs:Vect n a} -> Elem x (take (fS k) (x :: xs))
takeFSHasFirst = Here


data (<=) : Nat -> Nat -> Type where
  reflexive : {k : Nat} -> k <= k
  inc : {m,n : Nat} -> m <= n -> m <= (S n)

GEQZero : Nat -> Type
GEQZero k = 0 <= k

zeroLowerBound : All Nat (0 <=)
zeroLowerBound = induction (0 <=) reflexive (\k => inc {m=0} {n=k})