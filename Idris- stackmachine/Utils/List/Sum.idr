module Utils.List.Sum

import public Data.Vect

%default total
%access public export

||| Propositional sum.
|||
||| `sum . map f`
data Sum : (p : a -> Nat -> Type) -> (xs : List a) -> (sum : Nat) -> Type where
  Nil  : Sum p [] Z
  (::) : (hd : p x m) -> (tl : Sum p xs n) -> Sum p (x :: xs) (plus m n)
