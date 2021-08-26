module Utils.Str

import Data.Vect

import Utils.Vect.Sum
import Utils.Char
import Utils.Nat
import Utils.NotEq
import Utils.Ord

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data Str : Type where
  MkStr : Vect strlen Char.Char -> Str

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- [DecEq] ----------------------------------------------------------------------------------------

absurd_0 : (nNEQm : (m = n) -> Void) -> (MkStr {strlen=n} xs = MkStr {strlen=m} ys) -> Void
absurd_0 nNEQm Refl = nNEQm Refl

decEq : (x : Str) -> (y : Str) -> Dec (x = y)
decEq (MkStr {strlen = n} xs) (MkStr {strlen = m} ys) =
  case decEq m n of
    No mNEQn => No (absurd_0 mNEQn)
    Yes Refl =>
      case decEq xs ys of
        No  xsNEQys => No (\Refl => xsNEQys Refl)
        Yes Refl    => Yes Refl

-- [Strings are Totally Ordered] ------------------------------------------------------------------

||| x < y
data LTStr : (x : Str) -> (y : Str) -> Type where
  IsLTStr : (s1Rv1 : Sum CharAsNat s1 v1)
         -> (s2Rv2 : Sum CharAsNat s2 v2)
         -> (lt    : LTNat v1 v2) -- I wonder if this will be a bottleneck too?
         -> LTStr (MkStr s1) (MkStr s2)

isLTStr_gte : (s1Rv1   : Sum CharAsNat s1 v1)
           -> (s2Rv2   : Sum CharAsNat s2 v2)
           -> (gte : Not (LTNat v1 v2))
           -> LTStr (MkStr s1) (MkStr s2)
           -> Void
isLTStr_gte s1Rv1 s2Rv2 gte (IsLTStr p q lte)
  with (lemma_Sum_injective lemma_CharAsNat_injective s1Rv1 p,
        lemma_Sum_injective lemma_CharAsNat_injective s2Rv2 q)
    | (Refl, Refl) = gte lte

isLTStr : (x : Str) -> (y : Str) -> Dec (LTStr x y)
isLTStr (MkStr s1) (MkStr s2) with (sum charAsNat s1, sum charAsNat s2)
  | (Element v1 s1Rv1, Element v2 s2Rv2) with (isLTNat v1 v2)
    | No gte = No (isLTStr_gte s1Rv1 s2Rv2 gte)
    | Yes lt = Yes (IsLTStr s1Rv1 s2Rv2 lt)

singLTStr : (x,y : Str) -> (p,q : LTStr x y) -> p = q
singLTStr (MkStr s1) (MkStr s2)
          (IsLTStr {v1} {v2} s1Rv1_p s2Rv2_p lt_p) (IsLTStr s1Rv1_q s2Rv2_q lt_q) =
  case (lemma_Sum_injective lemma_CharAsNat_injective s1Rv1_p s1Rv1_q,
        lemma_Sum_injective lemma_CharAsNat_injective s2Rv2_p s2Rv2_q) of
    (Refl, Refl) =>
      case (lemma_Sum_singleton lemma_CharAsNat_singleton s1Rv1_p s1Rv1_q,
            lemma_Sum_singleton lemma_CharAsNat_singleton s2Rv2_p s2Rv2_q,
            singLTNat v1 v2 lt_p lt_q) of
        (Refl, Refl, Refl) => Refl

irreflLTStr : (x : Str) -> (p : LTStr x x) -> Void
irreflLTStr (MkStr s) (IsLTStr {v1} s1Rv1 s2Rv2 v1LTv2) =
  case (lemma_Sum_injective lemma_CharAsNat_injective s1Rv1 s2Rv2) of
    Refl =>
      case (lemma_Sum_singleton lemma_CharAsNat_singleton s1Rv1 s2Rv2) of
        Refl => irreflLTNat v1 v1LTv2

antisymLTStr : (x,y : Str) -> (p : LTStr x y) -> (q : LTStr y x) -> Void
antisymLTStr (MkStr s1) (MkStr s2)
             (IsLTStr {v1} {v2} s1Rv1_p s2Rv2_p v1LTv2_p)
             (IsLTStr {v1=v3} {v2=v4} s1Rv1_q s2Rv2_q v1LTv2_q) =
  case (lemma_Sum_injective lemma_CharAsNat_injective s1Rv1_p s2Rv2_q,
        lemma_Sum_injective lemma_CharAsNat_injective s2Rv2_p s1Rv1_q) of
    (Refl, Refl) => antisymLTNat v1 v2 v1LTv2_p v1LTv2_q

TotalOrderingStr : TotalOrdering Str
TotalOrderingStr = MkTotOrd LTStr isLTStr singLTStr irreflLTStr antisymLTStr decEq

---------------------------------------------------------------------------------------------------
-- [NotEq] ----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

lemma_NotEqStr_injective : (p : NotEq TotalOrderingStr x y f)
                        -> (q : NotEq TotalOrderingStr x y g)
                        -> f = g
lemma_NotEqStr_injective (IsLT p) (IsLT q) = Refl
lemma_NotEqStr_injective (IsGT p) (IsGT q) = Refl
lemma_NotEqStr_injective {x = MkStr x} {y = MkStr y}
                         (IsLT (IsLTStr p1 p2 p3)) (IsGT (IsLTStr q1 q2 q3)) =
  case (lemma_Sum_injective lemma_CharAsNat_injective p1 q2,
        lemma_Sum_injective lemma_CharAsNat_injective p2 q1) of
    (Refl, Refl) => lemma_NotEqNat_injective (IsLT p3) (IsGT q3)
lemma_NotEqStr_injective {x = MkStr x} {y = MkStr y}
                         (IsGT (IsLTStr p1 p2 p3)) (IsLT (IsLTStr q1 q2 q3)) =
  case (lemma_Sum_injective lemma_CharAsNat_injective p1 q2,
        lemma_Sum_injective lemma_CharAsNat_injective p2 q1) of
    (Refl, Refl) => lemma_NotEqNat_injective (IsGT p3) (IsLT q3)

lemma_NotEqStr_singleton : (p,q : NotEq TotalOrderingStr x y f) -> p = q
lemma_NotEqStr_singleton {x = MkStr x} {y = MkStr y}
                         (IsLT (IsLTStr {v1} {v2} p1 p2 p3)) (IsLT (IsLTStr q1 q2 q3)) =
  case (lemma_Sum_injective lemma_CharAsNat_injective p1 q1,
        lemma_Sum_injective lemma_CharAsNat_injective p2 q2) of
    (Refl, Refl) =>
      case (lemma_Sum_singleton lemma_CharAsNat_singleton p1 q1,
            lemma_Sum_singleton lemma_CharAsNat_singleton p2 q2) of
        (Refl, Refl) =>
          case singLTNat v1 v2 p3 q3 of
            Refl => Refl
lemma_NotEqStr_singleton {x = MkStr x} {y = MkStr y}
                         (IsGT (IsLTStr {v1} {v2} p1 p2 p3)) (IsGT (IsLTStr q1 q2 q3)) =
  case (lemma_Sum_injective lemma_CharAsNat_injective p1 q1,
        lemma_Sum_injective lemma_CharAsNat_injective p2 q2) of
    (Refl, Refl) =>
      case (lemma_Sum_singleton lemma_CharAsNat_singleton p1 q1,
            lemma_Sum_singleton lemma_CharAsNat_singleton p2 q2) of
        (Refl, Refl) =>
          case singLTNat v1 v2 p3 q3 of
            Refl => Refl
lemma_NotEqStr_singleton (IsLT p) (IsGT q) impossible
lemma_NotEqStr_singleton (IsGT p) (IsLT q) impossible

---------------------------------------------------------------------------------------------------
-- [Relations] ------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data StrLen : Str -> Nat -> Type where
  MkStrLen : {xs : Vect k Char.Char} -> StrLen (MkStr xs) k

data StrEmpty : Str -> Type where
  MkStrEmpty : StrEmpty (MkStr [])

data StrSplit : Str -> Char.Char -> Vect k Char.Char -> Type where
  MkStrSplit : StrSplit (MkStr (x :: xs)) x xs

---------------------------------------------------------------------------------------------------
-- [Convenience Functions] ------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

fromString' : Vect n Char -> Maybe (Vect n Char.Char)
fromString' [] = Just []
fromString' (x :: xs) = do
  Element (k,i) y <- isPChar x
  ys              <- fromString' xs
  pure (MkChar y :: ys)


fromString : String -> Maybe Str
fromString s = do
  xs <- fromString' (fromList (unpack s))
  pure (MkStr xs)

toString : Str -> String
toString (MkStr s) = pack (map toChar s)
