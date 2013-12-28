module DecEq

-- apparently this already exists in Decidable.Equality! Yay!

infixl 6 =~

public
class Equal a where
  (=~) : (x:a) -> (y:a) -> Dec (x = y)


private 
predZAbsurd : Z = S k -> _|_
predZAbsurd refl impossible


instance Equal Nat where
  Z =~ Z = Yes refl
  Z =~ (S k) = No predZAbsurd
  (S k) =~ Z = No (predZAbsurd . sym)
  (S n) =~ (S m) with (n =~ m)
    | Yes p = Yes (cong p)
    | No not = No (\ p => not (succInjective n m p))