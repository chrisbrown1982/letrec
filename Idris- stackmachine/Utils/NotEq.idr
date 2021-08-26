module Utils.NotEq

import Utils.Ord

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| Proof that two values of the same type are not (propositionally) equal.
|||
||| Takes advantage of the fact that the given type is totally ordered to avoid equality proofs;
||| specifically, x ≠ y iff (x > y) \/ (x < y).
data NotEq : (ord : TotalOrdering c)
          -> (x   : c)
          -> (y   : c)
          -> (f   : SOrdering)
          -> Type where
  IsLT : (lt : proj_LT ord x y) -> NotEq ord x y LT
  IsGT : (gt : proj_LT ord y x) -> NotEq ord x y GT

decNotEq_xEQy : (nlt : Not (proj_LT ord x y))
            -> (ngt : Not (proj_LT ord y x))
            -> (f ** (NotEq ord x y f))
            -> Void
decNotEq_xEQy nlt ngt (LT ** (IsLT lt)) = nlt lt
decNotEq_xEQy nlt ngt (GT ** (IsGT gt)) = ngt gt

decNotEq : (ord : TotalOrdering c) -> (x,y : c) -> Dec (f ** (NotEq ord x y f))
decNotEq ord x y with (proj_isLT ord x y)
  | Yes lt = Yes (LT ** (IsLT lt))
  | No nlt with (proj_isLT ord y x)
    | Yes gt = Yes (GT ** (IsGT gt))
    | No ngt = No (decNotEq_xEQy nlt ngt)

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

lemma_NotEq_sound : (p : NotEq ord x y f) -> Not (x = y)
lemma_NotEq_sound {ord} {x} (IsLT lt) Refl = proj_irrefl ord x lt
lemma_NotEq_sound {ord} {x} (IsGT gt) Refl = proj_irrefl ord x gt

lemma_NotEq_singleton : (ord : TotalOrdering c) -> (x : c) -> (y : c) -> (f : SOrdering)
                     -> (p : NotEq ord x y f) -> (q : NotEq ord x y f) -> p = q
lemma_NotEq_singleton ord x y LT (IsLT p) (IsLT q) =
  case proj_sing ord x y p q of Refl => Refl
lemma_NotEq_singleton ord x y GT (IsGT p) (IsGT q) =
  case proj_sing ord y x p q of Refl => Refl

lemma_NotEq_irreflexive : (p : NotEq ord x x f) -> Void
lemma_NotEq_irreflexive {ord} {x} (IsLT lt) = proj_irrefl ord x lt
lemma_NotEq_irreflexive {ord} {x} (IsGT gt) = proj_irrefl ord x gt

{-
lemma_NotEq_injective : (ord : TotalOrdering c) -> (x, y : c) -> (f1, f2 : SOrdering)
                     -> (p : NotEq ord x y f1) -> (q : NotEq ord x y f2) -> f1 = f2
lemma_NotEq_injective ord x y LT LT (IsLT p) (IsLT q) = Refl
lemma_NotEq_injective ord x y LT GT (IsLT p) (IsGT q) = ?holeHere
                                          -- this leads to a contradiction so it's *not* injective
                                          -- Maybe it's only injective for specific instances of c
                                          -- i.e. where we know the constructors of LT and can
                                          -- get the type checker to understand that this clause
                                          -- is impossible.
                                          -- Would need to define this for Char and Nat.

-- lemma_NotEq_injective ord x y LT f2 (IsLT lt) q = ?holeHere
-}
