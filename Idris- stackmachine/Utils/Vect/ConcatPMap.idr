module Utils.Vect.ConcatPMap

import public Data.Vect

%default total
%access public export

||| Propositional concatMap with an additional constraint argument defining the length of the vect.
|||
||| @q .
||| @p .
||| @xs .
||| @yss .
data ConcatPMap : (q   : a -> Nat -> Type)
               -> (p   : {k : Nat} -> (x : a) -> q x k -> Vect k c -> Type)
               -> (xs  : Vect n a)
               -> (yss : (m : Nat  ** Vect m c))
               -> Type where
  Nil  : ConcatPMap _ _ [] (Z ** [])
  (::) : {a  : Type}
      -> {q  : a -> Nat -> Type}
      -> {p  : {k : Nat} -> (w : a) -> q w k -> Vect k c -> Type}
      -> (r  : q x m)
      -> (hd : p x r ys)
      -> (tl : ConcatPMap q p xs (m_tl ** yss))
      -> ConcatPMap q p (x :: xs) ((m + m_tl) ** (ys ++ yss))

concatPMap : (q  : a -> Nat -> Type)
          -> (g  : (x : a) -> Subset Nat (q x))
          -> (p  : {k : Nat} -> (x : a) -> q x k -> Vect k c -> Type)
          -> (f  : {k : Nat} -> (x : a) -> (l : q x k) -> Subset (Vect k c) (p x l))
          -> (xs : Vect n a)
          -> Subset (m ** Vect m c) (ConcatPMap q p xs)
concatPMap q g p f [] = Element (Z ** []) Nil
concatPMap q g p f (x :: xs) with (g x)
  | Element len prf_len with (f x prf_len)
    | Element y prf_y with (concatPMap q g p f xs)
      | Element (len_tl ** tl) prf_tl =
        Element (len + len_tl ** y ++ tl) ((::) prf_len prf_y prf_tl)


{-
concatPMap : (q  : a -> Nat -> Type)
          -> (p  : {m : Nat} -> (x : a) -> q x m -> Vect m c -> Type)
          -> (g  : (y : a) -> Subset Nat (q x))
          -> (f  : (z : a) -> (l : q z m) -> Subset (Vect m c) (p z l))
          -> (xs : Vect n a)
          -> Subset (Vect (n * m) c) (ConcatPMap q p xs)
concatPMap q p g f [] = Element [] Nil
concatPMap q p g f (w :: ws) with (concatPMap q p g f ws)
  | (Element tl p_tl) with (g w)
    | (Element l p_l) = ?holeHere
-}
