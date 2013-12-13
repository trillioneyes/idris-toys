module Play

import Data.Vect

{-
data Elem : a -> Vect n a -> Type where
  here : {xs : Vect n a} -> Elem x (x :: xs)
  there : {xs:Vect n a} -> {x,y:a} -> Elem x xs -> Elem x (y :: xs)
-}

whereIsElem : {xs:Vect n a} -> Elem x xs -> (i ** index i xs = x)
whereIsElem Here = (fZ ** refl)
whereIsElem (There p) with (whereIsElem p)
  | (i ** p') = (fS i ** ?itemAtIndexIsEqual)


someGnats : Vect 5 Nat
someGnats = [0,1,2,3,4]

gnat3 : Elem 3 someGnats
gnat3 = There (There (There Here))

unGnat9 : Elem 9 someGnats -> _|_
unGnat9 (There (There (There (There (There p))))) with (whereIsElem p)
  | (i ** _) = FinZAbsurd i




which : {xs:Vect n a} -> Elem x xs -> (k:Fin (S n)) ->
       Either (Elem x (take k xs)) (Elem x (drop k xs))
which {a=a} p fZ ?= Right p{a=a}
which {a=a} Here _ ?= Left (Here{a=a})
which (There p) (fS i) with (which p i)
  | Left p' = Left (There p')
  | Right p' = Right p'

data Unique : Vect n a -> Type where
  none : {a : Type} -> Unique [] {a=a}
  more : {xs:Vect n a, x:a} -> Unique xs -> Not (Elem x xs) -> Unique (x :: xs)

---------- Proofs ----------

Play.itemAtIndexIsEqual = proof
  intros
  compute
  trivial


