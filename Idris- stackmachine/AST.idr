module AST

import Data.Vect

%default total
%access public export

data Exp : Type where
  Num   : Nat    -> Exp
  VarE  : Nat -> Exp         -- x   ---> semantic phase --> 4
  VarAE : Nat -> Nat -> Exp  -- a[4]
  Plus  : Exp    -> Exp -> Exp
  Min   : Exp    -> Exp -> Exp
  Mul   : Exp    -> Exp -> Exp
  And   : Exp    -> Exp -> Exp
  Or    : Exp    -> Exp -> Exp
  Eq    : Exp    -> Exp -> Exp
  Gt    : Exp    -> Exp -> Exp
  Gte   : Exp    -> Exp -> Exp

data NonInductiveExp : (e : Exp) -> Type where
  IsNum   : NonInductiveExp (Num n)
  IsVarE  : NonInductiveExp (VarE x)
  IsVarAE : NonInductiveExp (VarAE xs len)

data Stm : Type where
  VarDeclare    : Nat -> Nat -> Stm  -- int x = 42;  --> 4  -- declaration
  ArrayDeclare  : Nat -> Nat -> Stm  -- int a[42]; 
  Assign        : Exp -> Exp -> Stm   -- x = 45 ; -- asignment  

  If            : Exp -> Vect n Stm -> Vect m Stm -> Stm
  While         : Exp -> Vect n Stm -> Stm
  For           : Stm -> Exp -> Stm -> Vect n Stm -> Stm



FP : Type
FP = Nat

Env : {n : Nat} -> Type
Env {n} = Vect n Nat

Unique : Type
Unique = Nat
