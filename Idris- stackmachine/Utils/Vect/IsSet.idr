module Utils.Vect.IsSet

import Data.Vect

import Utils.Vect.NotElem
import Utils.Ord

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| Proof that a given vector has no duplicate (totally ordered) elements.
data IsSet : (ord : TotalOrdering c) -> (xs : Vect n c) -> Type where
  Nil  : IsSet ord []
  (::) : (here : NotElem ord x xs fs) -> (there : IsSet ord xs) -> IsSet ord (x :: xs)

---------------------------------------------------------------------------------------------------
-- [Decision Procedure] ---------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

decIsSet_here : (nhere : Not (fs ** NotElem ord x xs fs))
             -> IsSet ord (x :: xs)
             -> Void
decIsSet_here nhere ((::) {fs} here there) = nhere (fs ** here)

decIsSet : (ord : TotalOrdering c) -> (xs : Vect n c) -> Dec (IsSet ord xs)
decIsSet ord [] = Yes Nil
decIsSet ord (x :: xs) with (isNotElem ord x xs)
  | No nhere = No (decIsSet_here nhere)
  | Yes (fs ** here) with (decIsSet ord xs)
    | No nthere = No (\(_ :: there) => nthere there)
    | Yes there = Yes (here :: there)

---------------------------------------------------------------------------------------------------
-- [DecEq] ----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

decEqIsSet_neq : {neq_p  : NotElem ord x xs fs_y}
              -> {neq_q  : NotElem ord x xs fs_z}
              -> {p      : IsSet ord xs}
              -> (neq_fs : Not (fs_y = fs_z)) -> (neq_p :: p = neq_q :: p) -> Void
decEqIsSet_neq neq_fs Refl = neq_fs Refl

implementation DecEq (IsSet ord xs) where
  decEq Nil Nil = Yes Refl
  decEq {ord} {xs = (x :: xs)} ((::) {fs=fs_y} neq_p p) ((::) {fs=fs_z} neq_q q) =
    case decEq p q of
      No neq_tlset => No (\Refl => neq_tlset Refl)
      Yes Refl =>
      case decEq fs_y fs_z of
        No neq_fs => No (decEqIsSet_neq neq_fs)
        Yes Refl =>
          case lemma_NotElem_singleton ord x xs fs_y neq_p neq_q of
            Refl => Yes Refl

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

{- Doesn't work because NotEq is not injective.
lemma_Set_singleton : (p,q : IsSet ord xs) -> p = q
lemma_Set_singleton Nil Nil = Refl
lemma_Set_singleton {xs = (x :: xs)} ((::) {fs=fs_p} p ps) ((::) {fs=fs_q} q qs) = ?holeHere
  -- case (lemma_NotElem_singleton ord x xs )
-}
