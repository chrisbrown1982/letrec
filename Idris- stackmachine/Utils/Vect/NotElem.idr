module Utils.Vect.NotElem

import Data.Vect
import Utils.NotEq
import Utils.Ord

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| A proof that some element is not in a vector.
data NotElem : (ord : TotalOrdering c)
            -> (x   : c)
            -> (xs  : Vect n c)
            -> (fs  : Vect n SOrdering)
            -> Type where
  Here  : NotElem ord x [] []
  There : (notHere  : NotEq ord x y f)
       -> (notLater : NotElem ord x ys fs)
       -> NotElem ord x (y :: ys) (f :: fs)

isNotElem_here : (here : Not (f ** NotEq ord x y f)) -> (fs ** NotElem ord x (y :: ys) fs) -> Void
isNotElem_here here ((f :: fs) ** (There notHere _)) = here (f ** notHere)

isNotElem_later : (there : Not (fs ** NotElem ord x ys fs))
               -> (fs ** NotElem ord x (y :: ys) fs)
               -> Void
isNotElem_later there ((f :: fs) ** (There _ notThere)) = there (fs ** notThere)

isNotElem : (ord : TotalOrdering c)
         -> (x : c)
         -> (xs : Vect n c)
         -> Dec (fs ** NotElem ord x xs fs)
isNotElem ord x [] = Yes ([] ** Here)
isNotElem ord x (y :: ys) with (decNotEq ord x y)
  | No  here                = No (isNotElem_here here)
  | Yes (f ** notHere) with (isNotElem ord x ys)
    | No  there                 = No (isNotElem_later there)
    | Yes (fs ** notThere) = Yes ((f :: fs) ** (There notHere notThere))

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

lemma_NotElem_sound : (p : NotElem ord x xs fs) -> Not (Elem x xs)
lemma_NotElem_sound Here x = absurd x
lemma_NotElem_sound (There notHere notLater) Here = lemma_NotEq_irreflexive notHere
lemma_NotElem_sound (There notHere notLater) (There later) = lemma_NotElem_sound notLater later

lemma_NotElem_singleton : (ord : TotalOrdering c)
                       -> (x   : c)
                       -> (xs  : Vect n c)
                       -> (fs  : Vect n SOrdering)
                       -> (p   : NotElem ord x xs fs)
                       -> (q   : NotElem ord x xs fs)
                       -> p = q
lemma_NotElem_singleton ord x [] [] Here Here = Refl
lemma_NotElem_singleton ord x (y :: ys) (f :: fs) (There p1 q1) (There p2 q2) =
  case (lemma_NotEq_singleton ord x y f p1 p2, lemma_NotElem_singleton ord x ys fs q1 q2) of
    (Refl, Refl) => Refl

{-
lemma_NotElem_injective : (ord : TotalOrdering c)
                       -> (x   : c)
                       -> (xs : Vect n c)
                       -> (fs1 : Vect n SOrdering)
                       -> (fs2 : Vect n SOrdering)
                       -> (p : NotElem ord x xs fs1)
                       -> (q : NotElem ord x xs fs2)
                       -> fs1 = fs2
lemma_NotElem_injective ord x [] [] [] Here Here = Refl
lemma_NotElem_injective ord x (y :: ys) (f1 :: fs1) (f2 :: fs2) (There p_1 p_2) (There q_1 q_2) =
  ?holeHere
-}