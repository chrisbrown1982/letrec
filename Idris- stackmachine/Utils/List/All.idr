module Utils.List.All

import public Data.Vect

%default total
%access public export

||| A proposition `p` holds for all elements in `xs`
data All : (p : a -> Type) -> (xs : List a) -> Type where
  Nil  : All p []
  Cons : (here : p x) -> (there : All p xs) -> All p (x :: xs)

decAll : (p : a -> Type) -> (decP : (x : a) -> Dec (p x)) -> (xs : List a) -> Dec (All p xs)
decAll p decP [] = Yes Nil
decAll p decP (x :: xs) with (decP x)
  | No contra = No (\(Cons here there) => contra here)
  | Yes here  with (decAll p decP xs)
    | No contra = No (\(Cons here there) => contra there)
    | Yes there = Yes (Cons here there)

mapAll : {p : a -> Type} -> (f : (x ** p x) -> b) -> (all : All p xs) -> Vect (length xs) b
mapAll f [] = []
mapAll f (Cons {x} here there) = f (x ** here) :: mapAll f there
