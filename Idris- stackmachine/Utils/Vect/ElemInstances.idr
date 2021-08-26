module Utils.Vect.ElemInstances

import Data.Vect

import Utils.Vect.Elem

import Utils.Char
import Utils.Ord

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Instances] ------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

ElemChar : (x     : Char.Char)
        -> (xs    : Vect n Char.Char)
        -> (mieqs : Vect n (Maybe SOrdering))
        -> (nums  : Vect n Quantity)
        -> Type 
ElemChar = Elem TotalOrderingChar
