module Utils

import public Data.Vect

import public Utils.Char
import public Utils.Decidability
import public Utils.DPair
import public Utils.Fin
import public Utils.Maybe
import public Utils.Nat
import public Utils.NotEq
import public Utils.Str

import public Utils.Vect.All
import public Utils.Vect.ConcatQMap
import public Utils.Vect.Elem
import public Utils.Vect.ElemInstances
import public Utils.Vect.Filter
import public Utils.Vect.IsSet
import public Utils.Vect.Map
import public Utils.Vect.Maximum
import public Utils.Vect.NotElem
import public Utils.Vect.NotElemInstances
import public Utils.Vect.Sum

%default total
%access public export

-- [Finite Sets] ----------------------------------------------------------------------------------

data IsZero : Fin n -> Type where
  MkIsZero : IsZero FZ

data IsOne : Fin n -> Type where
  MkIsOne : IsOne (FS FZ)

-- [DecEq] ----------------------------------------------------------------------------------------

implementation Uninhabited (Here = There later) where
  uninhabited Refl impossible

implementation DecEq (Elem x xs) where
  decEq Here Here = Yes Refl
  decEq Here (There later) = No absurd
  decEq (There later) Here = No (absurd . sym)
  decEq (There later) (There x) with (decEq later x)
    decEq (There x) (There x) | Yes Refl = Yes Refl
    decEq (There later) (There x) | No c = No (\Refl => c Refl)
