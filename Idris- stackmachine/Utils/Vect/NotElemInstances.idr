module Utils.Vect.NotElemInstances

import Utils.Ord
import Utils.Nat
import Utils.Char
import Utils.Str

import Data.Vect
import Utils.Vect.NotElem

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Instances] ------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

NotElemNat : (x : Nat) -> (xs : Vect n Nat) -> (fs : Vect n SOrdering) -> Type
NotElemNat = NotElem TotalOrderingNat

NotElemChar : (x : Char.Char) -> (xs : Vect n Char.Char) -> (fs : Vect n SOrdering) -> Type 
NotElemChar = NotElem TotalOrderingChar

NotElemStr : Str -> (xs : Vect n Str) -> (fs : Vect n SOrdering) -> Type
NotElemStr = NotElem TotalOrderingStr