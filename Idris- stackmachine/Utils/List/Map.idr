module Utils.List.Map

import public Data.Vect

%default total
%access public export

||| Propositional map.
|||
||| Two lists are related via the binary relation `p`.
data Map : (p : a -> b -> Type) -> (xs : List a) -> (ys : List b) -> Type where
  Nil  : Map p [] []
  Cons : (hd : p x y) -> (tl : Map p xs ys) -> Map p (x :: xs) (y :: ys)

map : (p       : a -> b -> Type)
    -> (f       : a -> b)
    -> (f_sound : (x : a) -> p x (f x))
    -> (xs      : List a)
    -> List b
map p f f_sound [] = []
map p f f_sound (x :: xs) = f x :: map p f f_sound xs

lemma_map_sound : (p       : a -> b -> Type)
                -> (f       : a -> b)
                -> (f_sound : (x : a) -> p x (f x))
                -> (xs      : List a)
                -> Map p xs (map p f f_sound xs)
lemma_map_sound p f f_sound [] = Nil
lemma_map_sound p f f_sound (x :: xs) = Cons (f_sound x) (lemma_map_sound p f f_sound xs)
