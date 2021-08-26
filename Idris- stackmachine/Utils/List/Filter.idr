module Utils.List.Filter

import public Data.Vect

%default total
%access public export

||| Propositional filter.
|||
||| Two lists are related via the unary relation `p` s.t. `ys` contains only those elements in
||| `xs` for which `p` holds.
data Filter : (p : a -> Type) -> (xs : List a) -> (ys : List (Subset a p)) -> Type where
  Nil :                                              Filter p [] []
  Yes : (hd : p x)       -> (tl : Filter p xs ys) -> Filter p (x :: xs) (Element x hd :: ys)
  No  : (hd : Not (p x)) -> (tl : Filter p xs ys) -> Filter p (x :: xs) ys

filter : (p  : a -> Type)
      -> (f  : (x : a) -> Dec (p x))
      -> (xs : List a)
      -> List (Subset a p)
filter p f [] = []
filter p f (x :: xs) with (f x)
  | Yes hd = Element x hd :: (filter p f xs)
  | No  hd = (filter p f xs)

lemma_filter_sound : (p : a -> Type)
                  -> (f : (x : a) -> Dec (p x))
                  -> (xs : List a)
                  -> Filter p xs (filter p f xs)
lemma_filter_sound p f [] = Nil
lemma_filter_sound p f (x :: xs) with (f x)
  | Yes hd = Yes hd (lemma_filter_sound p f xs)
  | No  hd = No  hd (lemma_filter_sound p f xs)

