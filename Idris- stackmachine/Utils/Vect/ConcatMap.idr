module Utils.Vect.ConcatMap

import public Data.Vect

%default total
%access public export

||| Propositional concatMap.
|||
||| `((concat . (map f)) : List a -> List b)` where `(f : a -> List b)`
data ConcatMap : (p   : a -> Vect m b -> Type)
              -> (xs  : Vect k a)
              -> (yss : Vect (k * m) b)
              -> Type where
  Nil  : ConcatMap p [] []
  (::) : (hd : p x ys) -> (tl : ConcatMap p xs yss) -> ConcatMap p (x :: xs) (ys ++ yss)

concatMap : (p       : a -> Vect m b -> Type)
         -> (f       : a -> Vect m b)
         -> (f_sound : (x : a) -> p x (f x))
         -> (xs      : Vect k a)
         -> Vect (k * m) b
concatMap p f f_sound [] = Nil
concatMap p f f_sound (x :: xs) = f x ++ concatMap p f f_sound xs

lemma_concatMap_sound : (p       : a -> Vect m b -> Type)
                     -> (f       : a -> Vect m b)
                     -> (f_sound : (x : a) -> p x (f x))
                     -> (xs      : Vect k a)
                     -> ConcatMap p xs (concatMap p f f_sound xs)
lemma_concatMap_sound p f f_sound [] = Nil
lemma_concatMap_sound p f f_sound (x :: xs) = (f_sound x) :: (lemma_concatMap_sound p f f_sound xs)

lemma_concatMap_same : {p : a -> Vect m b -> Type}
                    -> (p_same : {z : a} -> {zs1,zs2 : Vect m b}
                              -> (p1 : p z zs1) -> (p2 : p z zs2) -> (zs1 = zs2))
                    -> (r1     : ConcatMap p xs yss1)
                    -> (r2     : ConcatMap p xs yss2)
                    -> (yss1 = yss2)
lemma_concatMap_same p_same [] [] = Refl
lemma_concatMap_same p_same (hd1 :: tl1) (hd2 :: tl2) with (p_same hd1 hd2)
  | Refl with (lemma_concatMap_same p_same tl1 tl2)
    | Refl = Refl

