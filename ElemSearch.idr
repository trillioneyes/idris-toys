module ElemSearch
import Data.Vect

spares : {xs:Vect n a, ys:Vect m a} ->
        Elem x xs -> Elem x (xs ++ ys)
spares Here = Here
spares (There p) = There (spares p)

bury : {xs:Vect n a, ys:Vect m a} ->
       Elem x xs -> Elem x (ys ++ xs)
bury {m=Z} {ys=[]} p = p
bury {m=S depth} {ys=top :: dirt} p = There (bury p)

data IsPrefixOf : Vect n a -> Vect m a -> Type where
  followedBy : {pre:Vect n a} -> (post:Vect m a) -> IsPrefixOf pre (pre ++ post)

data IsSuffixOf : Vect n a -> Vect m a -> Type where
  precededBy : {post:Vect m a} -> (pre:Vect n a) -> IsSuffixOf post (pre++post)

-- A view of vectors?
data Cut : Vect n a -> Type where
  append : (pre : Vect n a, post : Vect m a) -> Cut (pre ++ post)

parts : {n,m:Nat} -> {xs:Vect (n+m) a} -> Cut xs ->
        (pre:Vect n a ** (post:Vect m a ** pre ++ post = xs))
parts (append pre post) = (pre ** (post ** refl))

before : {xs:Vect (n+m) a} -> Cut xs ->
         (pre:Vect n a ** IsPrefixOf pre xs)
before cut with (parts cut)
  | (pre ** (post ** p)) = (pre ** replace p (followedBy post))
before' : {xs:Vect (n+m) a} -> Cut xs -> Vect n a
before' = getWitness . before

after : {xs:Vect (n+m) a} -> Cut xs ->
        (post:Vect m a ** IsSuffixOf post xs)
after cut with (parts cut)
  | (pre ** (post ** p)) = (post ** replace p (precededBy pre))
after' : {xs:Vect (n+m) a} -> Cut xs -> Vect m a
after' = getWitness . after


which : {xs : Vect (n+m) a} -> (cut : Cut xs) -> Elem x xs ->
        Either (Elem x (before' cut)) (Elem x (after' cut))
which {n=Z} (append [] xs) p = Right p
which {n=S k} (append (x :: pre) xs) Here = Left Here
which {n=S k} (append (x :: pre) xs) (There p)
  with (which (append pre xs) p)
  | Left p' = Left (There p')
  | Right p' = Right p'