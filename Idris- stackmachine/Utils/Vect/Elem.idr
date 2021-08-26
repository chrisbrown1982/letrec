module Utils.Vect.Elem

import Data.Vect
import Utils.Vect.Map
import Utils.Vect.NotElem
import Utils.Maybe
import Utils.Ord
import Utils.NotEq

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data Quantity : Type where
  None : Quantity
  Last : Quantity
  More : Quantity

||| A proof that some element is found in a vector.
|||
||| Under this definition the proof points at *all* occurrences of the given element.
||| An alternative that points at only the *first* ocurrence of the given element would be equally
||| valid.
|||
||| Stricter than Data.Vect.Elem.
||| Designed to have the property that there is only one way to construct a value of `Elem` for a 
||| given `x` and `xs` .
|||
||| This strictness is useful, e.g., when constructing contradictions for `decEq` implementations.
|||
||| Note to self: I wonder if `flags_ieq` and `flags_num` could be made implicit.
data Elem : (ord       : TotalOrdering c)
         -> (x         : c)
         -> (xs        : Vect n c)
         -> (flags_ieq : Vect n (Maybe SOrdering))
         -> (flags_num : Vect n Quantity)
         -> Type where
  JustHere : (mieqsRieqs : Map Certainly mieqs ieqs)
          -> (notThere   : NotElem ord x ys ieqs)
          -> Elem ord x (x :: ys) (Nothing :: mieqs) (Last :: fs)
  JustThere : (notHere : NotEq ord x y ieq)
           -> (there   : Elem ord x ys mieqs fs)
           -> Elem ord x (y :: ys) (Just ieq :: mieqs) (More :: fs)
  HereAndThere : (there : Elem ord x ys ieqs fs)
              -> Elem ord x (x :: ys) (Nothing :: ieqs) (More :: fs)

---------------------------------------------------------------------------------------------------
-- [Decision Procedure] ---------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- [Helper Functions] -----------------------------------------------------------------------------

IsElemTy : (ord : TotalOrdering c) -> (x : c) -> (xs : Vect n c)
        -> (Vect n (Maybe SOrdering), Vect n Quantity)
        -> Type
IsElemTy ord x xs (fs_ieq, fs_num) = Elem ord x xs fs_ieq fs_num

implementation Uninhabited (IsElemTy ord x [] ([], [])) where
  uninhabited JustHere impossible
  uninhabited JustThere impossible
  uninhabited HereAndThere impossible

isElem_empty : Subset (Vect 0 (Maybe SOrdering), Vect 0 Quantity) (IsElemTy ord x []) -> Void
isElem_empty (Element ([], []) p) = absurd p

isElem_hereAndNotHere : (xNEQy : Not (x = y))
                     -> (xEQy  : Not (f ** NotEq ord x y f))
                     -> Subset (Vect (S len) (Maybe SOrdering), Vect (S len) Quantity) 
                               (IsElemTy ord x (y :: ys))
                     -> Void
isElem_hereAndNotHere xNEQy xEQy (Element ((Nothing :: mieqs), (Last :: fs))
                                          (JustHere mieqsRieqs notThere)) = xNEQy Refl
isElem_hereAndNotHere xNEQy xEQy (Element ((Just ieq :: mieqs), (More :: fs))
                                          (JustThere notHere there)) = xEQy (ieq ** notHere)
isElem_hereAndNotHere xNEQy xEQy (Element ((Nothing :: mieqs), (More :: fs))
                                          (HereAndThere there)) = xNEQy Refl

isElem_neitherHereNorThere : (xNEQy : Not (x = y))
                          -> (notThere : Not (Subset (Vect len (Maybe SOrdering),
                                                      Vect len Quantity)
                                                     (IsElemTy ord x ys)))
                          -> Subset (Vect (S len) (Maybe SOrdering), Vect (S len) Quantity)     
                                    (IsElemTy ord x (y :: ys))
                          -> Void
isElem_neitherHereNorThere xNEQy notThere (Element (Nothing :: mieqs, Last :: fs)
                                                   (JustHere mieqsRieqs p)) = xNEQy Refl
isElem_neitherHereNorThere xNEQy notThere (Element (Just ieq :: mieqs, More :: fs)
                                                   (JustThere notHere there)) =
  notThere (Element (mieqs,fs) there)
isElem_neitherHereNorThere xNEQy notThere (Element (Nothing :: mieqs, More :: fs)
                                                   (HereAndThere there)) = xNEQy Refl

isElem_thereAndNotThere : (there : Not (fs ** NotElem ord x ys fs))
                       -> (notThere : Not (Subset (Vect len (Maybe SOrdering), Vect len Quantity) 
                                                  (IsElemTy ord x ys)))
                       -> Subset (Vect (S len) (Maybe SOrdering), Vect (S len) Quantity)
                                 (IsElemTy ord x (x :: ys))
                       -> Void
isElem_thereAndNotThere there notThere (Element (Nothing :: mieqs, Last :: fs)
                                                (JustHere {ieqs} mieqsRieqs p)) =
  there (ieqs ** p)
isElem_thereAndNotThere there notThere (Element (Just ieq :: mieqs, More :: fs)
                                                (JustThere notHere p)) =
  lemma_NotEq_irreflexive notHere
isElem_thereAndNotThere there notThere (Element (Nothing :: mieqs, More :: fs)
                                                (HereAndThere p)) =
  notThere (Element (mieqs,fs) p)

map_ieqs : (ieqs : Vect n SOrdering) -> (mieqs ** Map Certainly mieqs ieqs)
map_ieqs [] = ([] ** Nil)
map_ieqs (ieq :: ieqs) with (map_ieqs ieqs)
  | (mieqs ** tl) = (Just ieq :: mieqs ** MkCertainly :: tl)

constructJustHere : {ys         : Vect len c}
                 -> (mieqs      : Vect len (Maybe SOrdering))
                 -> (mieqsRieqs : Map Certainly mieqs ieqs)
                 -> (notThere   : NotElem ord x ys ieqs)
                 -> Subset (Vect (S len) (Maybe SOrdering), Vect (S len) Quantity)
                           (IsElemTy ord x (x :: ys))
constructJustHere {len} mieqs mieqsRieqs notThere =
  Element (Nothing :: mieqs, Last :: (replicate len None)) (JustHere mieqsRieqs notThere)

-- [The Decision Procedure] -----------------------------------------------------------------------

isElem : (ord : TotalOrdering c)
      -> (x   : c)
      -> (xs  : Vect n c)
      -> Dec (Subset (Vect n (Maybe SOrdering), Vect n Quantity) (IsElemTy ord x xs))
isElem ord x [] = No isElem_empty
isElem ord x (y :: ys) =
  case proj_decEq ord x y of
    No xNEQy =>
      case decNotEq ord x y of
        No  xEQy             => No (isElem_hereAndNotHere xNEQy xEQy)
        Yes (ieq ** notHere) =>
          case isElem ord x ys of
            No notThere => No (isElem_neitherHereNorThere xNEQy notThere)
            Yes (Element (mieqs,nums) there) =>
              Yes (Element (Just ieq :: mieqs, More :: nums) (JustThere notHere there))
    Yes Refl =>
      case isElem ord x ys of
        No notThere =>
          case isNotElem ord x ys of
            No there => No (isElem_thereAndNotThere there notThere)
            Yes (ieqs ** positiveNotThere) =>
              let (mieqs ** mieqsRieqs) = map_ieqs ieqs in
                Yes (constructJustHere mieqs mieqsRieqs positiveNotThere)
        Yes (Element (mieqs,nums) there) => Yes (Element (Nothing :: mieqs, More :: nums)
                                                         (HereAndThere there))

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

lemma_Elem_singleton : (ord    : TotalOrdering c)
                    -> (x      : c)
                    -> (xs     : Vect n c)
                    -> (fs_ieq : Vect n (Maybe SOrdering))
                    -> (fs_num : Vect n Quantity)
                    -> (p      : Elem ord x xs fs_ieq fs_num)
                    -> (q      : Elem ord x xs fs_ieq fs_num)
                    -> p = q
lemma_Elem_singleton ord x (x :: ys) (Nothing :: ieqs_tl) (Last :: fs_tl)
                     (JustHere {ieqs = ieqs_p} r_p p) (JustHere {ieqs = ieqs_q} r_q q) =
  case lemma_Map_injective lemma_Certainly_injective r_p r_q of
    Refl =>
      case (lemma_Map_singleton lemma_Certainly_singleton r_p r_q,
            lemma_NotElem_singleton ord x ys ieqs_p p q) of
        (Refl, Refl) => Refl
lemma_Elem_singleton ord x (y :: ys) (Just ieq :: ieqs_tl) (More :: fs)
                     (JustThere neq_p p) (JustThere neq_q q) =
  case (lemma_NotEq_singleton ord x y ieq neq_p neq_q,
        lemma_Elem_singleton ord x ys ieqs_tl fs p q) of
    (Refl, Refl) => Refl
lemma_Elem_singleton ord x (x :: ys) (Nothing :: ieqs) (More :: fs)
                     (HereAndThere p) (HereAndThere q) =
  case lemma_Elem_singleton ord x ys ieqs fs p q of
    Refl => Refl

{-
lemma_Elem_injective : (ord     : TotalOrdering c)
                    -> (x       : c)
                    -> (xs      : Vect n c)
                    -> (fs1_ieq : Vect n (Maybe SOrdering))
                    -> (fs1_num : Vect n Quantity)
                    -> (fs2_ieq : Vect n (Maybe SOrdering))
                    -> (fs2_num : Vect n Quantity)
                    -> (p       : Elem ord x xs fs1_ieq fs1_num)
                    -> (q       : Elem ord x xs fs2_ieq fs2_num)
                    -> fs1_ieq = fs2_ieq
lemma_Elem_injective ord x (x :: ys)
                     (Nothing :: mieqs1) (Last :: nums1)
                     (Nothing :: mieqs2) (Last :: nums2)
                     (JustHere {ieqs=ieqs_p} p_1 p_2) (JustHere {ieqs=ieqs_q} q_1 q_2) = ?holeHere
-- lemma_Elem_injective ord x (x :: ys)
--                      (Nothing :: mieqs1) (Last :: nums1)
--                      (mieq2 :: mieqs2) (num2 :: nums2)
--                      (JustHere p_1 p_2) q = ?holeHere
-- lemma_Elem_injective ord x (y :: ys)
--                      (mieq1 :: mieqs1) (num1 :: nums1)
--                      (mieq2 :: mieqs2) (num2 :: nums2)
--                      p q = ?holeHere
-}
